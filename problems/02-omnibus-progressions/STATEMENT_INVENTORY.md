# Statement inventory

Names below lie in namespace `Omnibus`, unless indicated otherwise. This inventory distinguishes the author closure from separate reviewer additions.

## Main exports

- `global_image_count_exact` in [ExactImageCounts.lean](lean/ExactImageCounts.lean): `Nat.card {c : Chord // ActualImage c} = 6840`. `ActualImage` requires a valid source and selected descending move, without endpoint validity.
- `global_approachable_count_exact` in the same file: `Nat.card {c : Chord // chord c = true ∧ ActualImage c} = 2232`.
- `normalized_image_count_exact` and `normalized_approachable_count_exact` in the same file: ordered bass-zero endpoint counts 570 and 186.
- `universal_eight_type_bound` in [UniversalBounds.lean](lean/UniversalBounds.lean): for every chord function `c` and `n`, initial validity and `n` admissible transitions imply at most 8 types among positions `0,…,n`.
- `eight_type_bound_is_attained` in [SharpBounds.lean](lean/SharpBounds.lean): an initially valid function has seven admissible transitions and exactly 8 types in its first eight positions. Its later constant continuation is not asserted admissible.
- `universal_infinite_seven_type_bound` in [InfiniteRangeBound.lean](lean/InfiniteRangeBound.lean): admissibility of every natural-indexed transition implies at most 7 types in every prefix of length `N`, including zero.
- `infinite_seven_type_bound_is_sharp` in the same file: an infinite admissible witness satisfies the all-prefix bound and attains 7 in its first seven positions.
- `universal_seven_prefix_bound` in [UniversalBounds.lean](lean/UniversalBounds.lean): the weaker repetition consequence, equal types at indices `i < j ≤ 7`.
- `seven_prefix_bound_is_attained` and `infinite_witness_is_admissible` in [SharpBounds.lean](lean/SharpBounds.lean): a checked infinite witness with seven initial types and type at position 7 equal to that at position 1.

## Semantic bridges

- [Pilot.lean](lean/Pilot.lean): canonical natural-number pitch-class representation, chord predicate, moves, type, and finite witness.
- [NodeJoin.lean](lean/NodeJoin.lean): `nodes_exact` connects the 55-entry checked list to the intrinsic node set.
- [LocalQuotientLift.lean](lean/LocalQuotientLift.lean): exact successor semantics from every valid actual representative.
- [ClosedWalkBounds.lean](lean/ClosedWalkBounds.lean): generic bounds from closure and a nonterminal count. [UniversalBounds.lean](lean/UniversalBounds.lean) discharges every concrete premise.
- [PeriodicWitness.lean](lean/PeriodicWitness.lean): the 36-state ordered period for genuine infinite attainment.
- [ActualChordCardinality.lean](lean/ActualChordCardinality.lean), [BassNatCardinality.lean](lean/BassNatCardinality.lean), and count-semantic modules: bounded actual-chord equivalences, inverse membership semantics, disjoint slices, and the factor-twelve bijection. `Nat.card` is not using its zero-for-infinite-types convention.
- [Frozen manifest](reproducibility/FROZEN_AUTHOR_MANIFEST.json): 101 author modules in dependency order, with roots `SharpBounds`, `InfiniteRangeBound`, and `ExactImageCounts`.

## Separate reviewer additions

[IndependentAudit.lean](lean/IndependentAudit.lean) imports those roots unchanged. It proves `independent_fifty_five_types`, `independent_finite_start_unapproachable`, and `independent_infinite_start_unapproachable`. These are reviewer theorems, not additions to the author roots.

## Audit and exclusions

The lock records all 426 distinct named axiom audits, corresponding to 434 printed lines in the independent replay. Every expected dependency set is a subset of `propext`, `Classical.choice`, and `Quot.sound`; the wrapper checks every expected name and set.

The Python fixture additionally establishes 3240 valid ordered chords, 49 graph edges, and further diagnostics. Those figures are not promoted to author Lean theorems. The quotient convention, unapproachable starts, incomplete literature coverage, and unresolved Conjecture 1 remain material limitations. Historical pending-compilation comments are preserved byte-for-byte; current verification is governed by replay receipts.
