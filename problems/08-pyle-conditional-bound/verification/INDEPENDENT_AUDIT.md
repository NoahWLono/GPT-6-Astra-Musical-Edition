# Verification summary

## Exact proof scope

The main theorem is `Omnibus.RootMarked.full_range_cardinality`. It states that every fixed bass-down infinite actual chord walk with an admissible predecessor at its initial chord, equipped with any valid quality/inversion reading of every chord, has a finite set exactly equal to its complete harmonic-type range and cardinality between 3 and 6. Neither absolute roots nor an undefined extension event are counted.

The standard-library equivalent is `raw_three_to_six`, giving three pairwise distinct attained types and a length-at-most-six list covering every type. Root interpretations are checked against eleven literal third-stack templates and inversion indices; symmetric-root interpretations are independently selectable at each time.

## Compilation

- Lean: 4.32.2.
- Main bound modules: `RootMarkedBounds`, `RawReading`, `Cardinality`.
- Main exported axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- `sorryAx` and native-decision axioms absent from main exports.
- Fresh package rebuild: all 28 project modules passed, including optional witnesses and cardinality wrapper.
- Independent fresh source replay: all 26 main proof modules passed. Reviewer also independently reconstructed the finite chord, graph, root-reading, and separation computations.
- Independent replay reused standard Lean and cached Mathlib dependencies, not project objects. Mathlib commit: `905b95818eb32af7874a58b427f50c1711a5e96c`.

The sanitized independent source checks are recorded in `INDEPENDENT_RECEIPT.json`; the separate public-package replay appears in `PUBLIC_REPLAY.json`. The optional witness supplement also passed independent source rebuild and semantic review after the main freeze; matching hashes and standard axioms are recorded in the combined receipt and `formal/WitnessExportAudit.lean`.

## Additional witnesses

`Witnesses` exports infinite admissibility and reading proofs for 36-position periodic examples, a six-distinct-type prefix, a three-type covering set, and an infinite seven-type example whose start has no admissible predecessor. The universal bound combines with these finite certificates to establish endpoint attainment. A finite-only counterexample discussion is explanatory and is not advertised as a named Lean theorem in this package.

## Not established

- That the explicit hypotheses exactly equal Pyle's intended definition of generalized omnibus progression.
- A formal definition of the author's extension event.
- An established novelty or priority claim.
- Any mixed-direction lower bound or mirror-only theorem.

The correspondence question is retained as a question; it is not an author response or a resolved source interpretation.
