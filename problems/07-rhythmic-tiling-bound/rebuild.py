#!/usr/bin/env python3
"""Verify frozen sources and compile all project modules into a new directory."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean', required=True, type=Path)
p.add_argument('--mathlib', required=True, type=Path)
p.add_argument('--output', required=True, type=Path)
p.add_argument('--max-rss-mib', type=int, default=3584,
               help='Linux resident-memory limit per Lean process; 0 disables it')
a = p.parse_args()
base = Path(__file__).resolve().parent
manifest = json.loads((base / 'build_manifest.json').read_text())
lean = a.lean.resolve()
mathlib = a.mathlib.resolve()
version = subprocess.check_output([lean, '--version'], text=True)
if not re.search(r'version ' + re.escape(manifest['lean_version']) + r'[,)]', version):
    raise SystemExit('The Lean version does not match the pin.')
revision = subprocess.check_output(['git', '-C', mathlib, 'rev-parse', 'HEAD'], text=True).strip()
if revision != manifest['mathlib_commit']:
    raise SystemExit('The Mathlib revision does not match the pin.')
dest = a.output.resolve()
if dest.exists():
    raise SystemExit('Choose a new output directory; existing output is never overwritten.')
dest.mkdir(parents=True)
for name, digest in manifest['source_sha256'].items():
    data = (base / 'formal' / name).read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise SystemExit('Source checksum mismatch: ' + name)
    (dest / name).write_bytes(data)
paths = [dest, mathlib / '.lake/build/lib/lean']
paths += sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))
if not paths[1].is_dir():
    raise SystemExit('The pinned Mathlib dependency cache must be prepared first.')
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', '')
receipt = {'status': 'running', 'lean_version': manifest['lean_version'],
           'mathlib_commit': revision, 'project_objects_reused': False,
           'project_modules': manifest['project_modules'],
           'audit_fixtures': manifest['audit_fixtures'],
           'trusted_dependencies': 'Pinned compiler, standard-library and cached Mathlib/package objects; not rebuilt from source',
           'modules': [], 'export_axioms': {}}
for name in manifest['build_order']:
    log = dest / (name + '.log')
    command = [str(lean), '-j1',
               '-R', str(dest), '-o', name + '.olean', name + '.lean']
    exceeded = False
    peak_rss = 0
    with log.open('w') as out:
        child = subprocess.Popen(command, cwd=dest, env=env, stdout=out, stderr=subprocess.STDOUT)
        while child.poll() is None:
            if a.max_rss_mib:
                try:
                    resident_pages = int(Path('/proc', str(child.pid), 'statm').read_text().split()[1])
                    rss = resident_pages * os.sysconf('SC_PAGE_SIZE')
                    peak_rss = max(peak_rss, rss)
                    if rss > a.max_rss_mib * 1024**2:
                        exceeded = True
                        child.kill()
                except (FileNotFoundError, ProcessLookupError):
                    pass
            time.sleep(0.1)
        code = child.returncode
    text = log.read_text()
    unsafe = any(word in text for word in ['sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler'])
    receipt['modules'].append({'module': name, 'source_sha256': manifest['source_sha256'][name + '.lean'],
                               'exit_code': code, 'resource_limit_exceeded': exceeded, 'peak_rss_mib': round(peak_rss / 1024**2, 2)})
    for theorem, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        receipt['export_axioms'][theorem] = [x.strip() for x in axioms.split(',') if x.strip()]
    if code or unsafe or exceeded:
        receipt['status'] = 'failed'
        (dest / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        raise SystemExit('Replay failed at ' + name + '; inspect its local diagnostic file.')
    print(name + ': passed', flush=True)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if not receipt['export_axioms'] or any(set(v) - allowed for v in receipt['export_axioms'].values()):
    receipt['status'] = 'failed'
else:
    receipt['status'] = 'passed'
receipt['axioms_union'] = sorted({v for vs in receipt['export_axioms'].values() for v in vs})
(base_sources := {f.name: hashlib.sha256(f.read_bytes()).hexdigest() for f in (base / 'formal').glob('*.lean')})
if base_sources != manifest['source_sha256']:
    receipt['status'] = 'failed'
(dest / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
if receipt['status'] != 'passed':
    raise SystemExit('Source or axiom audit failed.')
print('All project modules and audit fixtures passed; source-only replay complete.')
