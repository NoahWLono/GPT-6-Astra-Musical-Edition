# Rebuilding the six-note one-exchange result

## What is and is not reproduced

`rebuild.py` freshly compiles every project source, including the independent
exact-statement fixture. It never imports a distributed project object, never downloads
dependencies, and never modifies a supplied Mathlib checkout. Existing Lean
and Mathlib/package objects remain trusted. This is not a from-source rebuild
of the compiler or Mathlib.

Both the historical independent replay and a complete replay using this exact
packaged wrapper passed. The latter compiled all 34 frozen sources with zero
project-object reuse in 86.060723 actual aggregate CPU seconds. The compiler-free
preflight and mocked-process static checks are recorded separately.

## Prepare the pinned environment

Use Linux x86_64 with Python 3.10 or later and git. Install the official
[Lean 4.32.2 Linux release](https://github.com/leanprover/lean4/releases/tag/v4.32.2),
or select `leanprover/lean4:v4.32.2` with an existing elan installation. The
wrapper requires the exact recorded Linux executable hash, not an elan shim.
For example, `elan which lean` from this project resolves the real executable.

Prepare Mathlib separately, following its official setup guidance. One standard
preparation route is:

```sh
git clone https://github.com/leanprover-community/mathlib4.git /path/to/mathlib4
git -C /path/to/mathlib4 checkout 905b95818eb32af7874a58b427f50c1711a5e96c
cd /path/to/mathlib4
lake exe cache get
```

Dependency acquisition needs network access and can consume substantial disk.
The dependency-preparation commands above are documented for users; they were
not rerun as part of packaging. Do not run `lake update` to change the locks.
Keep the Mathlib and dependency tracked worktrees clean. The wrapper checks
their exact git revisions, Mathlib's toolchain pin, and the byte-exact
`lake-manifest.json` supplied here as
`reproducibility/mathlib-lake-manifest.json`.

The Lean executable SHA256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The full machine-readable lock is
[`reproducibility/environment-lock.json`](reproducibility/environment-lock.json).

## Check and rebuild

From this project directory, verify the frozen proof-source bytes:

```sh
sha256sum -c SOURCE_SHA256SUMS
```

Run the compiler-free preflight, supplying your actual paths:

```sh
python3 rebuild.py --check-only \
  --lean /path/to/lean-4.32.2-linux/bin/lean \
  --mathlib /path/to/mathlib4
```

Then choose an output directory that does not already exist, whose parent
exists and has at least 4 GiB free:

```sh
python3 rebuild.py \
  --lean /path/to/lean-4.32.2-linux/bin/lean \
  --mathlib /path/to/mathlib4 \
  --output /path/to/new-homometry-replay
```

The output contains fresh copied sources, objects, a preflight record, per-module
logs and receipts, and `replay-ledger.json`. Only after all 34 compiler calls
and final axiom audits succeed is `RESULT.json` written with `status: passed`.
A failed or interrupted run leaves its evidence available. Choose another new
output path for a retry; the wrapper does not silently resume or reuse objects.

The resource envelope mirrors the independent replay: 19.5-second observed CPU
watchdog and 20-second hard CPU limit per process, 35-second wall limit per
process, `-M1900` Lean memory setting, 2-GiB sampled RSS, 64-MiB log/object output limit, 4-GiB free-disk floor,
and 180-second aggregate child CPU budget. Sampling cannot provide a hard RSS
ceiling. Slower machines may need a separately reviewed resource policy; a
resource-limit failure is not a mathematical disproof.

## Rebuild the paper

On a standard TeX Live installation with `geometry`, `amsmath`, `amssymb`,
`amsthm`, `booktabs`, `hyperref`, and TikZ:

```sh
sh build-paper.sh
```

This runs two `pdflatex` passes. TeX versions, font maps, and PDF metadata can
change PDF bytes without changing the manuscript. Inspect the generated pages
visually after rebuilding. The distributed six-page PDF was rebuilt after the requested author-label
update. Its mathematical text is unchanged from the audited source-and-paper
bundle; the author line, PDF metadata, and brief attribution note were updated.

## Optional bounded checks

```sh
cd computations
python3 independent_audit.py
python3 check_order_four.py
```

The first checks all normalized one-exchange pairs for `6 <= n <= 24` using
Lee-distance multiplicities, plus translations and reflections. The second
checks the order-four bracelet-pair formula through `n = 160`. These are bounded
consistency checks, not proof certificates. Their saved results are historical;
the independent script's output destination was changed to a portable relative
path for this package. The Lean sources were not changed.

## Reading historical evidence

Files in `verification/independent-replay/` are unchanged historical records.
Absolute paths and commands identify the original workspace; they are not
portable rebuild instructions. Original `sources/<module>.lean` paths map to
`lean/<module>.lean` here. A duplicate of the independent fixture is kept at
its historical evidence path to preserve the original evidence checksum check.
Historical object hashes identify fresh objects that are deliberately not
distributed. Use `rebuild.py` for a new portable replay.
