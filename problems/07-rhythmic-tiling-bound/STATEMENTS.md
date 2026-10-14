# Exact statements and limits

A monochromatic nonattacking placement of t queens on a k-by-k board satisfies `t² - 1 <= 3k(k - t)`. The same bound holds for transverse triplets in an actual perfect rhythmic triplet tiling: a partition of 0,...,3k-1 into positive-gap three-term arithmetic progressions with pairwise distinct gaps.

The formalization proves the injective-array estimate, its bridge to the actual exact-cover tiling, and the one-color queens theorem. It includes t = 0. Subtraction occurs over the real numbers, not truncated natural subtraction.

This is a complete proof of a supporting obstruction. Existence of perfect rhythmic triplet tilings for all sufficiently large orders remains unresolved. Novelty is unestablished. The square-root and asymptotic forms in the paper are manuscript-level corollaries, not separately named Lean theorems.

## Formal declarations

- `Rhythmic.partial_transverse_bound`: injective-array bound
- `Rhythmic.partial_transverse_bound_shifted`: shifted version
- `Rhythmic.PerfectTripletTiling.transverse_bound`: bound for transverse members of a genuine exact-cover tiling
- `Rhythmic.monochromatic_queens_bound`: same-color nonattacking queens bound

`formal/ExportAudit.lean` checks these exact declarations and their transitive axiom sets.
