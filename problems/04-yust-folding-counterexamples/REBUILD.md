# Rebuilding Yust folding counterexamples

The source-only entry point is `./check-publication.sh`. It checks the pinned
Lean and Mathlib versions, compiles the published project source into a fresh
temporary object, prints the source's axiom audit, and removes the object.
The existing Lean standard-library and Mathlib/package objects remain trusted;
this does not rebuild those dependencies from source.

## Lean

Use Lean **4.32.2** and a separately prepared Mathlib checkout at
`905b95818eb32af7874a58b427f50c1711a5e96c`, with its pinned dependencies and cache
already available. Official setup references:
[Lean releases](https://github.com/leanprover/lean4/releases/tag/v4.32.2) and
[Mathlib](https://github.com/leanprover-community/mathlib4).

```sh
MATHLIB_DIR=/path/to/mathlib4 \
LEAN_BIN=/path/to/lean-4.32.2/bin \
./check-publication.sh
```

`LEAN_BIN` may be omitted if the pinned compiler and Lake are already on PATH.
The check performs no downloads and does not edit the Mathlib checkout.
Sanitized human audit reports, JSON receipts, mathematical data, and source
hashes are retained as provenance. Raw logs and machine-specific paths are
excluded from the publication package.

## Paper

The published PDF and LaTeX are unchanged from the audited deliverable. With
TeX Live and the packages requested by the source installed, run:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error yust_folding_counterexamples.tex
pdflatex -interaction=nonstopmode -halt-on-error yust_folding_counterexamples.tex
```

The supplied `build-paper.sh` runs the same two standard TeX passes and, for
Project 04, copies the result to its published PDF location. This packaging run
syntax-checked the helper; it did not rebuild the unchanged, previously rendered
and inspected paper PDF.

## Computation and integrity

Python 3 runs the supplied search/verification sources. Read the project README
for their exact bounds and limitations; computations are separate from the Lean
certificate. From this folder, `sha256sum -c SHA256SUMS` checks publication file
integrity, not mathematical correctness. Generated build outputs are excluded.
