# Counterexamples to two folding characterizations

Status: both counterexamples established and independently audited; the frozen Lean certificate passed a fresh isolated rebuild. Research date: 14 October 2026. No claim of publication priority or novelty is made.

## Source and scope

Jason Yust, “Tetrachordal Folding Operations,” in *Mathematics and Computation in Music*, MCM 2022, pp. 292–303, DOI [10.1007/978-3-031-07015-0_24](https://doi.org/10.1007/978-3-031-07015-0_24). The [author-hosted revised paper](https://sites.bu.edu/jyust/files/2022/09/tetrachordalFoldingRev.pdf) states the two conjectures on its page 8.

In mathematical paraphrase, Conjecture 1 characterizes folding of equally sized pitch sets by two shared codimension-one subset types and all but one pairwise interval occurrence. Conjecture 2 proposes the analogous characterization for pitch-class sets, permitting either folding or T-shift.

The relevant conventions come from Proposition 4 and the preceding discussion (paper pp. 4–7): subset types are considered up to transposition and inversion, and interval content retains multiplicity. An n-note folding fixes n−1 notes, reflecting the remaining note about an inversion that preserves a selected n−2-note core. Definition 4 instead permits a translation symmetry of the core and moves the remaining note by an integer multiple of that translation.

The examples below use distinct pitches, two different shared subset types, exactly the required interval overlap, and inequivalent whole sets. Thus neither repetitions, equal-set degeneracies, nor “at least” versus “exactly” interpretations explain the failures.

## 1. Pitch-space Conjecture 1: a seven-note counterexample

Take, in integer pitch space,

- A = {0, 1, 2, 3, 6, 7, 9}
- B = {0, 1, 2, 3, 6, 8, 9}.

### Two shared six-note types

First,

A ∖ {7} = B ∖ {8} = {0, 1, 2, 3, 6, 9}.

Second, reflection I₉(x) = 9−x sends

A ∖ {2} = {0, 1, 3, 6, 7, 9}

to

B ∖ {1} = {0, 2, 3, 6, 8, 9}.

These six-note types are distinct. Both source subsets have minimum 0 and maximum 9. Any translation between them must be zero; any inversion must have index 9. Neither possibility maps one to the other.

### Exactly twenty shared intervals

The interval multiplicities for lengths 1,…,9 are

- A: (4, 3, 3, 2, 2, 3, 2, 1, 1)
- B: (4, 3, 3, 1, 2, 3, 2, 2, 1).

Their multiset intersection has cardinality 20 = C(7,2)−1. The only change is one occurrence of interval 4 to interval 8. In particular A and B are not related by transposition or inversion.

### No folding is possible

A folding would require an inversion-symmetric five-note subset of A. Such an odd finite symmetric set must contain its reflection center. A has no possible center supporting two distinct reflected pairs:

- Center 0 or 9: no pair
- Center 1: only {0,2}
- Center 2: only {1,3}
- Center 3: only {0,6}
- Center 6: only {3,9}
- Center 7: no pair.

Consequently every odd-cardinality inversion-symmetric subset of A has at most three notes. A therefore admits no seven-note folding to any target. Transposition or inversion of A cannot create a symmetric five-note subset, so allowing arbitrary representatives does not change the conclusion.

This disproves the proposed implication from shared content to folding.

### An infinite pitch-space family

The same construction works for each integer t ≥ 6:

- Aₜ = {0,1,2,3,t,t+1,t+3}
- Bₜ = {0,1,2,3,t,t+2,t+3}.

Their common six-set is obtained by deleting t+1 and t+2. Reflection Iₜ₊₃ maps Aₜ ∖ {2} to Bₜ ∖ {1}. Both source six-sets have endpoints 0,t+3, and neither the identity nor Iₜ₊₃ relates them.

Write Cₜ = {0,1,2,3,t,t+3}. The distances from the exceptional point t+1 to Cₜ are the multiset

{t+1,t,t−1,t−2,1,2},

whereas the distances from t+2 to Cₜ are

{t+2,t+1,t,t−1,2,1}.

Thus the full interval multisets exchange precisely t−2 for t+2. They share exactly twenty occurrences.

For the obstruction, an odd symmetric subset must be centered at a member of Aₜ. A center in the lower block {0,1,2,3} cannot have an upper-block partner except at t=6, center 3, for the pair {0,6}; that center has no pair wholly inside the lower block. Otherwise a lower-block center supports at most one pair within {0,1,2,3}. A center in the upper block cannot have a lower-block partner except at t=6, center 6, for the pair {3,9}; that center has no pair wholly inside the upper block. The upper block {t,t+1,t+3} contains no arithmetic-progression triple. Hence no center supports two pairs.

The infinite family is proved here in ordinary mathematics; the current Lean certificate proves the concrete t=6 instance, not the parameterized family.

## 2. Pitch-class Conjecture 2: a five-note counterexample

Work in Z/12Z and take

- P = {0,1,3,4,6}
- Q = {0,1,3,4,7}.

### Two shared four-note types

P ∖ {6} = Q ∖ {7} = {0,1,3,4}.

Also I₇(x) = 7−x modulo 12 sends

P ∖ {1} = {0,3,4,6}

to

Q ∖ {0} = {1,3,4,7}.

The two source subset types are different: {0,1,3,4} has two semitone pairs while {0,3,4,6} has one.

### Exactly nine shared interval classes

Their interval-class vectors, in the order ic1,…,ic6, are

- P: (2,2,3,1,1,1)
- Q: (2,1,3,2,1,1).

They share nine of ten occurrences, exchanging one ic2 for one ic4. Their different vectors also rule out whole-set T/I equivalence.

### No folding

The only inversion-symmetric three-note subset of P is {0,3,6}, whose inversion index is 6. The two remaining pitches are 1 and 4. Folding 1 sends it to 5, giving {0,3,4,5,6}; folding 4 sends it to 2, giving {0,1,2,3,6}. These outputs are themselves T/I-equivalent. Neither is T/I-equivalent to Q: both have interval vector (3,2,2,1,1,1), unlike Q.

### No T-shift

A nonidentity translation preserving a three-element subset of Z/12Z must have order three. Its orbits are the augmented triads {r,r+4,r+8}. P contains no such triad, so none of its three-note cores has a nonidentity translational symmetry. The identity translation leaves P unchanged, which is not T/I-equivalent to Q.

Every integer multiple of a core-stabilizing translation again stabilizes the core. Therefore checking every stabilizing translation, as the formal certificate does, includes all operations allowed by Definition 4.

This disproves the proposed implication from shared content to folding or T-shift.

## Formal certificate

`formal/Counterexamples.lean` uses Lean 4.32.2 and mathlib commit 905b95818eb32af7874a58b427f50c1711a5e96c. It models integer pitch sets as `Finset ℤ` and pitch-class sets as `Finset (Fin 12)` with modular arithmetic.

The file defines unordered pairwise interval multisets directly, retaining multiplicity. It checks cardinalities, distinct deletion types, non-equivalence of the full sets, exact overlaps, and failure of every relevant operation. The pitch-space obstruction proves that every possible integer reflection axis is in a finite interval before performing a finite check; it does not assume a bounded pitch universe. Additional lemmas cover all source T/I representatives and the integer-multiple form of T-shift.

All finite certificates use ordinary `decide`, checked by Lean’s kernel. There is no `sorry`, new axiom, `native_decide`, or external solver oracle in the proof. The only reported axioms are standard Lean/mathlib foundations: `propext`, `Classical.choice`, and `Quot.sound`.

The Python search is discovery/supporting evidence, not the proof dependency. Run `formal/check.sh` for the formal verification.

## Prior-art check and limits

The [author’s publications page](https://sites.bu.edu/jyust/Publications/) was checked on 14 October 2026 and contains entries through 2026. It still links the 2022 revised paper and its two 2022 presentations. Targeted public searches for the exact paper title, the title with “proof” or “counterexample,” and Yust/folding/Conjecture 1 or 2 found no later primary-source resolution. The Springer chapter landing page and presentation links were not readable through the available web retrieval tool.

This is a bounded literature check, not proof of originality or absence of earlier work. The result here is a refutation of the characterizations under the source’s stated operations. It does not classify all exceptional pairs, establish the smallest possible pitch-space counterexample, or prove a repaired characterization.
