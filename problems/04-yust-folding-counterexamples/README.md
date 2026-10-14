# Yust folding conjectures: counterexample package

Start with the five-page [PDF paper](output/pdf/yust_folding_counterexamples.pdf) or [RESEARCH_NOTE.md](RESEARCH_NOTE.md) for exact examples, elementary proofs, interpretation of the source statements, and limitations of the literature search.

## Results

1. Pitch-space Conjecture 1 fails at seven notes: `{0,1,2,3,6,7,9}` versus `{0,1,2,3,6,8,9}`.
2. Pitch-class Conjecture 2 fails in 12-TET at five notes: `{0,1,3,4,6}` versus `{0,1,3,4,7}`.

Both examples have two distinct shared codimension-one subset types and exactly all but one interval occurrence in common. The proof excludes arbitrary source and target transposition/inversion representatives, not just one alignment. A human proof of an infinite seven-note family is included; only its concrete `t=6` member is formally certified.

## Public rebuild

See [REBUILD.md](REBUILD.md) for the portable fresh-object check.

## Formal verification

- Lean: 4.32.2
- mathlib commit: `905b95818eb32af7874a58b427f50c1711a5e96c`
- Source: `formal/Counterexamples.lean`
- Main theorems: `YustFolding.conjecture_one_false` and `YustFolding.conjecture_two_false`

With the pinned Mathlib checkout and Lean toolchain prepared, run:

```sh
MATHLIB_DIR=/path/to/mathlib4 LEAN_BIN=/path/to/lean-4.32.2/bin ./formal/check.sh
```

On a separate machine with Elan/Lake installed, the pinned `lean-toolchain` and `lakefile.toml` support the `lake update`, `lake exe cache get`, and `lake build` workflow. The full all-representatives finite certificate can take a few minutes.

The proof uses ordinary kernel-checked `decide`, not `native_decide`. The Python search results are reproducible discovery evidence and are not imported into Lean.

## Files

- `RESEARCH_NOTE.md`: readable mathematical account and source audit
- `formal/Counterexamples.lean`: complete formal source, one module
- `formal/check.sh`: portable verification entry point
- `lakefile.toml`, `lean-toolchain`: dependency pins for an independent project
- `search.py`: exhaustive search over bounded integer sets or all sets in a finite modulus
- `search_pitch.jsonl`: bounded search, diameter at most 16, cardinalities 3–8
- `search_mod12.jsonl`: all 12-TET set classes, cardinalities 3–12

No claim that these examples are the first published counterexamples is made. The note records the bounded current primary-source search and does not infer novelty from unsuccessful searches.

## Independent audit

The frozen source passed an isolated independent rebuild in 74.84 seconds. See `audit/AUDIT_STATUS.md`, `audit/receipt.json`, and `audit/ExportAudit.lean`. No project object files were reused. The audit also checked the source-to-formal-statement correspondence and the ordinary mathematical proof of the infinite family.

The PDF was rendered and all five pages visually inspected. The actual LaTeX source is `paper/yust_folding_counterexamples.tex`; run `./build-paper.sh` to compile it. The paper credits GPT-6 Astra, explicitly identified as the project AI author label, and uses mathematical theorem/proof typesetting.

Raw compiler and console logs are omitted from the public package. The audit reports and JSON receipts record the verified results; the published source and audit harness reproduce the theorem and axiom checks.
