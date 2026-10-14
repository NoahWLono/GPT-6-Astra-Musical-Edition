# Rebuild and trust boundary

## Pinned dependencies

- Lean `4.32.2` (`leanprover/lean4:v4.32.2`)
- Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`
- Python 3.8 or later; Git

Install the pinned Lean release through its official distribution. Prepare a separate Mathlib checkout at the pinned commit, including its normal dependency cache:

```sh
git clone https://github.com/leanprover-community/mathlib4.git mathlib4
git -C mathlib4 checkout 905b95818eb32af7874a58b427f50c1711a5e96c
(cd mathlib4 && lake exe cache get)
```

The Lean and Lake executables on PATH for cache preparation must belong to Lean 4.32.2. The wrapper checks the Lean version and Mathlib commit, verifies every project source hash, and refuses to overwrite an existing output directory.

## Check the source release

From this project folder:

```sh
sha256sum -c SHA256SUMS
python3 rebuild.py --lean /path/to/lean-4.32.2/bin/lean --mathlib /path/to/mathlib4 --output /new/empty/build-directory
```

Use your own local paths. The output path must not already exist. The build compiles 20 project modules plus two audit fixtures in the frozen dependency order, using a single Lean worker and zero reused project objects. On Linux the default per-process resident-memory cutoff is 6144 MiB; `--max-rss-mib` can adjust that local resource limit. The broad imports and exact certificates require substantial memory. The wrapper writes a JSON receipt and local diagnostics to the output folder. Diagnostic logs are not part of this public release.

The wrapper verifies that all exported transitive axioms are among `propext`, `Classical.choice`, and `Quot.sound`, and rejects proof-placeholder/native-decision trust markers in diagnostics. The stored [publication receipt](verification/PUBLIC_REPLAY.json) records an INCOMPLETE source-only replay. Fourteen modules completed; CompactGlobalB6 was stopped at the 6144 MiB resident-memory limit, and the remaining seven modules/fixtures were not attempted. A full pass of this new wrapper is not claimed. The original independent rebuild did pass all 20 project modules plus the independent aggregate and export audit, on exactly the frozen sources published here. No project objects from another build were introduced into the resource-limited replay. A higher local memory limit may be necessary for a complete reproduction.

## Paper

Use a LaTeX distribution with pdfLaTeX, Latin Modern, and the packages listed in the source preamble. From `paper/`, run pdfLaTeX twice on `difference-table-structural-partial.tex`. The supplied PDF is the original completed artifact; a later rebuild may differ in metadata or font packaging.

## Trust boundary

Project sources are freshly compiled. The pinned Lean compiler, its standard library, cached Mathlib, and package dependencies are reused; they are not rebuilt from source. Hashes identify the exact source bytes and artifacts, not mathematical novelty or peer review. The exact research scope and manuscript-only deductions are described in [STATEMENTS.md](STATEMENTS.md).
