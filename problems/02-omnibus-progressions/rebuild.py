#!/usr/bin/env python3
"""Rebuild the frozen 102-source closure without reusing project objects.

Linux, Python 3.10+, git, the pinned Lean release, and a prepared pinned
Mathlib checkout are required. This program never downloads dependencies.
Use --check-only to validate source and dependency pins without invoking Lean.
"""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CPU_PER_MODULE = 20
CPU_AGGREGATE = 400
WALL_PER_MODULE = 35
RSS_LIMIT = 2 * 1024**3
OUTPUT_LIMIT = 64 * 1024**2
DISK_FLOOR = 4 * 1024**3


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def json_write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def without_comments(text):
    # Frozen inputs use ordinary Lean nested block and line comments.
    out, depth, i = [], 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, "Unterminated source comment")
    return "".join(out)


def preflight(args):
    require(sys.platform.startswith("linux"), "The bounded wrapper requires Linux /proc")
    lock_path = ROOT / "reproducibility/environment-lock.json"
    lock = json.loads(lock_path.read_text())
    lean = args.lean.resolve(strict=True)
    mathlib = args.mathlib.resolve(strict=True)
    require(digest(lean) == lock["lean_linux_x86_64_binary_sha256"],
            "Lean binary hash differs from the recorded Linux x86_64 release")
    require(digest(ROOT / "lean-toolchain") == lock["lean_toolchain_sha256"],
            "Local toolchain pin changed")
    require(digest(mathlib / "lean-toolchain") == lock["lean_toolchain_sha256"],
            "Mathlib toolchain pin differs")
    require(git(mathlib, "rev-parse", "HEAD") == lock["mathlib_commit"],
            "Mathlib commit differs")
    require(not git(mathlib, "status", "--porcelain", "--untracked-files=no"),
            "Mathlib has tracked modifications")
    manifest_path = mathlib / "lake-manifest.json"
    require(digest(manifest_path) == lock["mathlib_lake_manifest_sha256"],
            "Mathlib dependency lock differs")
    require(digest(ROOT / "reproducibility/mathlib-lake-manifest.json") ==
            lock["mathlib_lake_manifest_sha256"], "Bundled dependency lock changed")
    manifest = json.loads(manifest_path.read_text())
    libraries = [mathlib / ".lake/build/lib/lean", lean.parent.parent / "lib/lean"]
    dependencies = []
    for package in manifest["packages"]:
        path = mathlib / manifest["packagesDir"] / package["name"]
        require(git(path, "rev-parse", "HEAD") == package["rev"],
                f"Dependency commit differs: {package['name']}")
        require(not git(path, "status", "--porcelain", "--untracked-files=no"),
                f"Dependency has tracked modifications: {package['name']}")
        library = path / ".lake/build/lib/lean"
        if library.is_dir():
            libraries.append(library)
        dependencies.append({"name": package["name"], "commit": package["rev"]})
    require(all(p.is_dir() for p in libraries), "Mathlib objects are not prepared")

    source_dir = ROOT / "lean"
    order = lock["replay_order"]
    require(len(order) == len(set(order)) == 102, "Expected 102 distinct modules")
    require({p.name for p in source_dir.iterdir()} == set(lock["source_sha256"]),
            "Source directory must contain exactly the 102 frozen .lean files")
    require((ROOT / "reproducibility/replay-order.txt").read_text().splitlines() == order,
            "Replay order differs from lock")
    require(set(lock["source_sha256"]) == {m + ".lean" for m in order},
            "Source lock and module order disagree")
    seen, external_imports = set(), set()
    for module in order:
        source = source_dir / (module + ".lean")
        require(digest(source) == lock["source_sha256"][source.name],
                f"Frozen source changed: {source.name}")
        code = without_comments(source.read_text())
        require(not re.search(r"\b(sorry|admit|axiom|native_decide)\b", code),
                f"Forbidden proof token: {module}")
        for line in code.splitlines():
            if not re.match(r"^\s*import\s", line):
                continue
            for dependency in line.split()[1:]:
                if dependency in order:
                    require(dependency in seen, f"Import order violation: {module}")
                else:
                    require((dependency.startswith("Mathlib.") or dependency == "Std"),
                            f"Unexpected external import: {dependency}")
                    external_imports.add(dependency)
        seen.add(module)
        for library in libraries:
            require(not (library / (module + ".olean")).exists(),
                    f"External path contains a project object: {module}")
    external_objects = []
    for module in sorted(external_imports):
        relative = Path(*module.split(".")).with_suffix(".olean")
        matches = [p / relative for p in libraries if (p / relative).is_file()]
        require(len(matches) == 1, f"Missing or ambiguous external object: {module}")
        external_objects.append({"module": module, "object_sha256": digest(matches[0])})
    return lock, lean, libraries, {
        "status": "preflight_passed",
        "compiler_invoked": False,
        "environment_lock_sha256": digest(lock_path),
        "module_count": len(order),
        "mathlib_commit": lock["mathlib_commit"],
        "dependencies": dependencies,
        "direct_external_objects": external_objects,
        "trust_boundary": lock["trust_boundary"],
    }


def parse_audits(text):
    audits = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S):
        audits[match[1]] = [x.strip() for x in match[2].split(",") if x.strip()]
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        audits[match[1]] = []
    return audits


def compile_module(lean, source, output, log, env, aggregate):
    remaining = CPU_AGGREGATE - aggregate
    require(remaining > 0.5, "Aggregate CPU budget exhausted")
    cpu_hard = min(CPU_PER_MODULE, max(1, math.ceil(remaining)))
    watchdog = min(CPU_PER_MODULE - 0.5, remaining - 0.1)

    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_hard, cpu_hard))
        resource.setrlimit(resource.RLIMIT_FSIZE, (OUTPUT_LIMIT, OUTPUT_LIMIT))

    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start, peak, reason = time.monotonic(), 0, None
    command = [str(lean), "-j1", "-o", str(output), source.name]
    with log.open("wb") as stream:
        proc = subprocess.Popen(command, cwd=source.parent, env=env, stdout=stream,
                                stderr=subprocess.STDOUT, preexec_fn=limits,
                                start_new_session=True)
        try:
            while proc.poll() is None:
                cpu = rss = 0
                try:
                    pdir = Path("/proc") / str(proc.pid)
                    stat = (pdir / "stat").read_text()
                    fields = stat[stat.rfind(")") + 2:].split()
                    cpu = (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")
                    for line in (pdir / "status").read_text().splitlines():
                        if line.startswith("VmRSS:"):
                            rss = int(line.split()[1]) * 1024
                except (FileNotFoundError, ProcessLookupError):
                    pass
                peak = max(peak, rss)
                output_size = sum(p.stat().st_size for folder in (output.parent, log.parent)
                                  for p in folder.iterdir() if p.suffix in (".olean", ".log"))
                if time.monotonic() - start > WALL_PER_MODULE:
                    reason = "wall_limit"
                elif cpu >= watchdog:
                    reason = "cpu_limit"
                elif rss > RSS_LIMIT:
                    reason = "rss_limit"
                elif output_size > OUTPUT_LIMIT:
                    reason = "output_limit"
                elif shutil.disk_usage(output.parent).free < DISK_FLOOR:
                    reason = "disk_floor"
                if reason:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    break
                time.sleep(0.02)
        finally:
            if proc.poll() is None:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            code = proc.wait()
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime
    wall = time.monotonic() - start
    peak_children_rss = after.ru_maxrss * 1024
    final_output_size = sum(p.stat().st_size for folder in (output.parent, log.parent)
                                  for p in folder.iterdir() if p.suffix in (".olean", ".log"))
    if reason is None:
        if aggregate + cpu > CPU_AGGREGATE:
            reason = "aggregate_cpu_limit"
        elif cpu > cpu_hard:
            reason = "cpu_hard_limit"
        elif peak_children_rss > RSS_LIMIT:
            reason = "rss_limit"
        elif wall > WALL_PER_MODULE:
            reason = "wall_limit"
        elif final_output_size > OUTPUT_LIMIT:
            reason = "output_limit"
        elif shutil.disk_usage(output.parent).free < DISK_FLOOR:
            reason = "disk_floor"
    # A killed writer can leave an incomplete final UTF-8 character.
    text = log.read_text(errors="replace")
    audits = parse_audits(text)
    bad = {name: values for name, values in audits.items()
           if set(values) - ALLOWED_AXIOMS}
    return {
        "module": source.stem, "exit_code": code, "stop_reason": reason,
        "cpu_seconds": round(cpu, 6),
        "aggregate_cpu_seconds": round(aggregate + cpu, 6),
        "wall_seconds": round(wall, 6),
        "peak_sampled_rss_bytes": peak, "cumulative_child_maxrss_bytes": peak_children_rss, "source_sha256": digest(source),
        "object_sha256": digest(output) if output.exists() else None,
        "log_sha256": digest(log), "axiom_audits": audits,
        "forbidden_axioms": bad, "sorry_warning": "declaration uses 'sorry'" in text,
        "command": command,
        "limits": {"cpu_hard_seconds": cpu_hard, "cpu_watchdog_seconds": watchdog,
                   "aggregate_cpu_seconds": CPU_AGGREGATE,
                   "wall_seconds": WALL_PER_MODULE, "rss_bytes": RSS_LIMIT,
                   "output_bytes": OUTPUT_LIMIT, "disk_floor_bytes": DISK_FLOOR},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path, help="Pinned Linux Lean executable")
    parser.add_argument("--mathlib", required=True, type=Path, help="Prepared pinned Mathlib checkout")
    parser.add_argument("--output", type=Path, help="A new directory; existing paths are refused")
    parser.add_argument("--check-only", action="store_true", help="Preflight only; never invoke Lean")
    args = parser.parse_args()
    lock, lean, libraries, pre = preflight(args)
    if args.check_only:
        print(json.dumps(pre, indent=2))
        return
    require(args.output is not None, "Choose a fresh --output directory")
    output = args.output.absolute()
    require(not output.exists(), "Output directory already exists; choose a new path")
    require(shutil.disk_usage(output.parent).free >= DISK_FLOOR, "Less than 4 GiB free disk")
    output.mkdir()
    sources, objects, logs = (output / n for n in ("sources", "objects", "logs"))
    sources.mkdir()
    objects.mkdir()
    logs.mkdir()
    for module in lock["replay_order"]:
        shutil.copyfile(ROOT / "lean" / (module + ".lean"), sources / (module + ".lean"))
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    env["LEAN_PATH"] = os.pathsep.join(map(str, [objects, *libraries]))
    pre["lean_path"] = env["LEAN_PATH"].split(os.pathsep)
    pre["fresh_project_object_directory"] = str(objects)
    json_write(output / "preflight.json", pre)
    records, aggregate, audits = [], 0.0, {}
    for module in lock["replay_order"]:
        source = sources / (module + ".lean")
        require(digest(source) == lock["source_sha256"][source.name], "Copied source differs")
        record = compile_module(lean, source, objects / (module + ".olean"),
                                logs / (module + ".log"), env, aggregate)
        records.append(record)
        aggregate += record["cpu_seconds"]
        audits.update(record["axiom_audits"])
        json_write(output / "replay-ledger.json", records)
        json_write(logs / (module + ".receipt.json"), record)
        print(f"{module}: exit={record['exit_code']}, CPU={record['cpu_seconds']:.6f}s", flush=True)
        require(record["exit_code"] == 0 and record["stop_reason"] is None and
                not record["forbidden_axioms"] and not record["sorry_warning"] and
                record["object_sha256"] is not None and
                record["source_sha256"] == lock["source_sha256"][source.name],
                f"Replay failed at {module}; inspect {logs}")
    for name, expected in lock["expected_audits"].items():
        require(name in audits and set(audits[name]) == set(expected),
                f"Missing or changed final axiom audit: {name}")
    result = {
        "status": "passed", "project_modules": 101, "independent_fixtures": 1,
        "project_objects_reused": 0, "actual_aggregate_cpu_seconds": round(aggregate, 6),
        "named_axiom_audit_count": sum(len(r["axiom_audits"]) for r in records),
        "final_axioms": {n: audits[n] for n in lock["expected_audits"]},
        "replay_ledger_sha256": digest(output / "replay-ledger.json"),
        "environment_lock_sha256": pre["environment_lock_sha256"],
        "trust_boundary": lock["trust_boundary"],
    }
    json_write(output / "RESULT.json", result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
