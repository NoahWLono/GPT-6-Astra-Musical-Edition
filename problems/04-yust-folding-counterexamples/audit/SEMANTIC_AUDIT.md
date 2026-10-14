# Yust folding counterexample semantic audit

Source: Jason Yust, Tetrachordal Folding Operations, https://sites.bu.edu/jyust/files/2022/09/tetrachordalFoldingRev.pdf . Relevant printed pages: 4 (general folding and symmetric-core requirement), 5 (Proposition 4 and shared T/I subset types), 7 (Definition 4, T-shift), 8 (Conjectures 1 and 2).

The finite-set models match the relevant counterexample conditions. Integer pitch intervals count absolute differences of unordered pairs, with multiplicity. Pitch-class intervals count the smaller modular distance, likewise with multiplicity. This reading is supported by the source's treatment of duplicated intervals. Two shared deletion types are inequivalent under T/I, not just two occurrences of the same type. The source explicitly describes the subset types as generalized over inversion.

A generalized fold fixes n-1 points and reflects the remaining point about an inversion stabilizing an n-2 core. Selecting two distinct deletions a,b defines exactly that core, and insert(t-a, S.erase(a)) is the resulting point set. Permitting arbitrary T/I equivalence of the output is at least as permissive as literal fixed-position folding. Source representative changes are handled by affine conjugation: an isometry sends inversion-stable cores to inversion-stable cores and conjugates the point reflection to another reflection. Folding is reversible when the output retains the original cardinality.

Definition 4's multiple of a stabilizing transposition still stabilizes the same core. Testing every stabilizing transposition directly therefore includes all allowed multiples (and conversely one may choose that transposition itself with multiplier one). Allowing identity shifts or collapsed intermediate sets only enlarges the relation; nonexistence is consequently not weakened by these choices.

The pitch no-core proof bounds the inversion INDEX t, not the axis t/2. If a nonempty subset S of [0,9] satisfies t-S=S, then taking x in S gives t=x+(t-x) in [0,18]. Thus checking those integer indices is exhaustive, rather than silently restricting an unbounded integer quantifier. Any reflection preserving a nonempty integer set has an integer inversion index, even if axes are described geometrically as real numbers.

Independent enumeration confirms:
- Pitch A={0,1,2,3,6,7,9}, B={0,1,2,3,6,8,9}: cardinality7, non-T/I-equivalent, exactly two shared six-note T/I types, 20 shared unordered interval occurrences, one4 exchanged for one8, and no inversion-symmetric five-note subset of A.
- Pitch-class A={0,1,3,4,6}, B={0,1,3,4,7}: cardinality5, non-T/I-equivalent, exactly two shared four-note T/I types, 9 shared interval-class occurrences, and no fold or T-shift to the T/I class of B.

The counterexamples concern a single folding or T-shift operation, not connectivity by arbitrary sequences. They refute the forward implication of the printed arbitrary-cardinality conjectures under the source's stated conventions. They do not affect the proved tetrachordal proposition. No novelty or priority conclusion is included in this audit. Fresh Lean compilation and exact export/axiom results are recorded separately once the source is frozen.

## Final frozen-source verification

PASS: independently compiled the sole project module from source in this audit directory, with no reused project object. Source SHA256 a884ebb6566c9920f3890c3b9b331a84c7e4a168404482847992a59b92217ace. Lean4.32.2 and cached upstream mathlib905b95818eb32af7874a58b427f50c1711a5e96c were reused. Build completed in74.84seconds, exit0. Final negated conjecture types and definitions, source-representative lemmas, and literal integer-multiple T-shift bridge were separately printed and inspected. All depend only on propext, Classical.choice, Quot.sound. No sorry/admit/new axiom/native_decide/unsafe/extern bypass appears in the project source.

The conjecture predicates restrict to n>=3 and inequivalent whole-set types, require two different shared deletion types and exact multiset overlap, and allow all source T/I representatives. Thus the counterexamples avoid the apparent small-cardinality, equality, type-count and representative ambiguities. The pitch-index bound quantifies over all integer indices before deriving the finite bound.

One prose defect was found and corrected before delivery: A does have even-cardinality symmetric subsets (for example A without1 is symmetric under index9). The corrected note asserts only that every ODD-cardinality symmetric subset has at most3elements. The formal no-five theorem was always correct. The t>=6 infinite pitch-family argument was reviewed and is valid with the odd-cardinality restriction; it is a human mathematical proof, not part of the Lean certificate.
