# Exact omnibus image counts and sharp descending-walk bounds

This package gives **new exact answers** to Section V of [Pyle (2025)](https://musmat.org/journal/v9/02-Pyle.pdf): **6840 actual move endpoints**, of which **2232 are valid approachable ordered chords**. It also proves sharp **8-type finite** and **7-type infinite** descending-walk bounds under an explicit bass-relative quotient convention.

**The novelty claim concerns the numerical counts 6840 and 2232.** The [documented prior-art search](PRIOR_ART_COMPARISON.md), conducted through 13 October 2026, found no earlier matching answer to Pyle’s Section V numerical questions. Its coverage is incomplete, so this is a bounded novelty assessment, not a first-ever priority claim. The count interpretation is independent of the quotient used for the walk bounds. No novelty claim is made here for the 8/7 bounds, and these results do not solve or disprove Pyle’s Conjecture 1.

Author label: **GPT-6 Astra**. This is the project’s AI-author label, not a statement of the underlying runtime model or affiliation with OpenAI. See [attribution](ATTRIBUTION.md).

## Read and verify

- [Paper (PDF)](paper/omnibus_bounds.pdf) and [LaTeX source](paper/omnibus_bounds.tex)
- [Statement inventory](STATEMENT_INVENTORY.md) and [independent semantic review](SEMANTIC_REVIEW.md)
- [Rebuild instructions](REBUILD.md), [bounded wrapper](rebuild.py), and [environment lock](reproducibility/environment-lock.json)
- [Independent replay report](INDEPENDENT_REPLAY_REPORT.md) and [evidence guide](verification/README.md)

## Exact domain and counts

An ordered chord is `(b,t,a,s)` in `(Z/12Z)^4`; voice positions and repetitions matter. A chord is valid if some ordering stacks either three distinct pitch classes with one doubled note using exactly one zero and two intervals in `{3,4}`, or four distinct pitch classes with all three intervals in `{3,4}`. This implements Pyle’s Definitions 4–5.

A descending move lowers the bass by one and raises exactly one upper voice by one, modulo 12. Let `Q` be the valid ordered chords and `I = f_T(Q) ∪ f_A(Q) ∪ f_S(Q)`. The checked results are `|I| = 6840` and `|Q ∩ I| = 2232`. The first count allows invalid targets; the second requires endpoint validity. Both count distinct actual ordered endpoints, not edges, source/voice pairs, quotient types, or root-marked interpretations.

The identity question has an explicit membership criterion: an endpoint lies in `I` precisely when at least one of its three inverse-move predecessors is valid. To be approachable it must also belong to `Q`. This criterion is formalized; the package does not print all 2232 chords.

Bass-zero normalization preserves upper-voice order. The normalized cardinalities are 570 and 186; an explicit bijection proves the factor 12. No division by six or assumption of free upper-voice permutations is used.

## Exact walk convention

The type of `(b,t,a,s)` is the sorted triple `((t−b),(a−b),(s−b)) mod 12`. It forgets common transposition and upper-voice order, retaining bass-relative inversion and multiplicity. Admissible descending transitions require both endpoints in `Q`.

- Every finite admissible walk visits at most 8 distinct types; an eight-position walk attains 8.
- Every finite prefix of every infinite admissible walk visits at most 7 distinct types. A checked infinite witness attains 7 and has a 36-state ordered-chord periodic tail.
- Both witnesses start at the valid but **unapproachable** chord `(0,0,3,6)`. They do not establish sharpness with an approachable initial chord.

The closure contains 101 byte-frozen author modules plus one separate reviewer module. No project object is distributed or reused by the wrapper. Existing pinned Lean, standard-library, Mathlib, and package objects remain trusted. See the evidence guide for both the independent and packaged-wrapper replay status.

Complete SCC/cycle classification, a modulo-three lower endpoint, and identification of this quotient with Pyle’s extension/sonority conventions are outside this result. Auxiliary Python counts are computational evidence, not additional Lean exports.
