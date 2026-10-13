# Reproduce the frozen omnibus results

## Trust boundary

`rebuild.py` compiles all 101 author modules and the separate reviewer `IndependentAudit` into a new object directory. It never downloads dependencies, edits the supplied checkout, resumes an old run, or imports a distributed project object. Existing pinned Lean, standard-library, Mathlib, and package objects remain trusted. This is not a from-source compiler/Mathlib bootstrap.

The historical independent replay passed all 102 compilations plus a separately written finite reconstruction in 295.343323 aggregate child CPU seconds. Its evidence is separate from the public-wrapper replay; see [verification/README.md](verification/README.md) for wrapper status.

## Prepare dependencies

Use Linux x86_64, Python 3.10+, git, the official [Lean 4.32.2 release](https://github.com/leanprover/lean4/releases/tag/v4.32.2), and prepared Mathlib at commit `905b95818eb32af7874a58b427f50c1711a5e96c`. The actual Lean executable SHA256 must be `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. An elan shim is not the executable; `elan which lean` can resolve the actual path.

A standard preparation route is:

```sh
git clone https://github.com/leanprover-community/mathlib4.git /path/to/mathlib4
git -C /path/to/mathlib4 checkout 905b95818eb32af7874a58b427f50c1711a5e96c
cd /path/to/mathlib4
lake exe cache get
```

These are instructions for a new environment, not operations rerun during packaging. They require network and substantial disk. Keep tracked dependency worktrees clean and do not run `lake update`. The wrapper checks exact dependency revisions, the toolchain pin, bundled `reproducibility/mathlib-lake-manifest.json`, all source hashes, import order, absence of colliding project objects in external paths, and direct external objects.

## Preflight and fresh replay

From this package directory:

```sh
sha256sum -c SOURCE_SHA256SUMS
python3 rebuild.py --check-only \
  --lean /path/to/lean-4.32.2-linux/bin/lean \
  --mathlib /path/to/mathlib4
```

Choose a nonexistent output directory whose parent exists and has at least 4 GiB free:

```sh
python3 rebuild.py \
  --lean /path/to/lean-4.32.2-linux/bin/lean \
  --mathlib /path/to/mathlib4 \
  --output /path/to/new-omnibus-replay
```

The output records copied sources, fresh objects, per-module logs/receipts, preflight data, and `replay-ledger.json`. Only complete success writes `RESULT.json` with `status: passed`, including all 426 named axiom dependency checks. A failure stops the run and preserves evidence; a retry requires a new path and separately appropriate resources.

Limits: 19.5-second observed CPU watchdog / 20-second hard CPU per compiler, 35-second wall per compiler, 2-GiB RSS monitoring, `-j1`, 64-MiB combined generated compiler logs/objects, 4-GiB disk floor, and 400-second aggregate compiler child CPU. RSS sampling is supplemented by the kernel child high-water mark at completion. This is not an adversarial process-tree sandbox. A slower machine may need a separately reviewed envelope; resource failure is not a mathematical counterexample.

## Independent computational regression

The portable adapter performs the archived reviewer reconstruction, changing only source/output path handling:

```sh
python3 computations/independent_fixture_audit.py \
  --output /path/to/new-fixture-results.json
```

It independently reconstructs states, checks local quotient semantics from every representative and all frozen successor equations, searches visited-set walks, and checks both witnesses. It loads no Lean objects. Auxiliary numerical diagnostics are computational evidence, not new theorem exports.

## Paper

Use TeX Live with `lmodern`, `microtype`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `booktabs`, `array`, `enumitem`, `hyperref`, and `fancyhdr`:

```sh
sh build-paper.sh
```

This performs two PDFLaTeX passes. TeX version, fonts, and timestamps can change PDF bytes. Source/PDF hashes and visual QA are recorded separately. The paper build never modifies Lean sources.

## Historical records

Archived commands retain original workspace paths and are evidence, not portable instructions. Their `sources/<name>.lean` corresponds to `lean/<name>.lean` here. Historical objects are not distributed; receipts retain their hashes. The original checksum list is `SHA256SUMS.original-run.txt`; use package-root `SHA256SUMS` for distributed files and `SOURCE_SHA256SUMS` for the 102 proof inputs.
