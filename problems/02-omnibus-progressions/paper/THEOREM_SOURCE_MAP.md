# Paper and theorem source map

The final paper is `omnibus_bounds.tex` and its rendered eight-page PDF is `omnibus_bounds.pdf`. Its AI-author label is GPT-6 Astra; the title-page note distinguishes this project label from runtime identity and OpenAI affiliation. All paths below are relative to this paper directory. No Lean source was edited or compiled during paper preparation.

## Main mathematical claims

| Paper statement | Checked declaration or evidence | Scope |
|---|---|---|
| Definition 1: intrinsic permitted chords | `../lean/Pilot.lean`: `stacking`, `reorderings`, `chord` | All 24 permutations, bounded canonical pitch classes; exactly the source's triads/sevenths predicate |
| Three descending moves and admissibility | `../lean/Pilot.lean`: `step`, `OmnibusStep` | Both endpoints valid; only bass-down and one-upper-up steps |
| Definition 2: explicit type quotient | `../lean/Pilot.lean`: `sort3`, `sonority`; translation/canonical/symmetry bridge modules | Bass-relative upper multiset; retains multiplicity and bass identity; no root labels |
| Lemma 3: exact local lifting | `../lean/LocalQuotientLift.lean`: `Omnibus.local_quotient_lift` | Both directions from every actual valid representative |
| Complete 55-node list | `../lean/NodeJoin.lean`: `nodes_exact`, `chord_type_in_nodes`; additional `../lean/IndependentAudit.lean` node-cardinality check | Intrinsic candidate enumeration, not an assumed graph |
| All successor sets in Appendix A | `../lean/EdgeSlice0.lean` through `../lean/EdgeSlice6.lean`: `successor_0` through `successor_54` | Actual successor function computed from intrinsic chord/move definitions |
| Equation (1): small closed certificates | `../lean/ClosureSlice0.lean` through `../lean/ClosureSlice6.lean`; `../lean/UniversalBounds.lean`: `every_node_has_small_nonterminal_closure` | Each initial vertex is in a successor-closed list with at most seven nonterminal entries |
| Lemma 4: generic closed-set bound | `../lean/ClosedWalkBounds.lean`: `finite_distinct_bound`, `infinite_distinct_bound`, `infinite_repeat_by_seven` | Abstract closure hypotheses, discharged by the concrete certificates |
| Theorem 5: finite bound 8 | `../lean/UniversalBounds.lean`: `Omnibus.universal_eight_type_bound` | Every finite admissible walk, counting all distinct visited types, repetitions allowed |
| Theorem 5: every infinite prefix has at most 7 types | `../lean/InfiniteRangeBound.lean`: `Omnibus.universal_infinite_seven_type_bound` | Every natural-number prefix, including the empty prefix |
| Theorem 5: repeated type at indices i<j≤7 | `../lean/UniversalBounds.lean`: `Omnibus.universal_seven_prefix_bound` | Pigeonhole consequence; weaker than the all-prefix bound |
| Theorem 6: eight-type finite attainment | `../lean/SharpBounds.lean`: `Omnibus.eight_type_bound_is_attained` | First seven transitions of an eight-position witness |
| Theorem 6: genuinely infinite attainment | `../lean/SharpBounds.lean`: `infinite_witness_is_admissible`, `seven_prefix_bound_is_attained`; `../lean/InfiniteRangeBound.lean`: `infinite_seven_type_bound_is_sharp` | Admissible at every natural index; seven distinct first types; repeat of index 1 at index 7 |
| Explicit 36-move periodic lift | `../lean/PeriodicWitness.lean`: `periodStates`, `concrete_period_is_admissible`; `../computations/periodic_witness.json` | Paper word is the literal movement sequence of the checked 36-state array |
| Equation (4): effective image/approachability criterion | `../lean/CountTranslation.lean`: `image_membership`; `../lean/ActualChordCardinality.lean`: `actualImage_iff` | Actual bounded ordered endpoint iff at least one permitted inverse-move source exists |
| Bass normalization and factor 12 | `../lean/BassPackedEquiv.lean`, `../lean/BassPredicateEquiv.lean`, `../lean/BassNatCardinality.lean` | Explicit mutually inverse maps, preserving upper-voice order; no free-S3-action assumption |
| Raw-list generator correctness | `../lean/ImageEnumerationSemantics.lean`: `sourceRaw_membership`, `imageRaw_membership` | Repeated raw-list entries do not affect semantic membership |
| Disjoint slices and cardinalities | `../lean/ImageSliceSemantics.lean`; `../lean/DisjointSliceCardinality.lean` | Duplicate-free slices connected to intrinsic predicates and subtype cardinalities |
| Table 2 exact counts | `../lean/ImageCountSlice0.lean` through `../lean/ImageCountSlice11.lean`; `../lean/ExactImageCounts.lean`: `image_tenor_counts`, `approachable_tenor_counts` | All 12 tenor rows in both columns, not a graph-type count |
| Normalized counts 570 and 186 | `../lean/ExactImageCounts.lean`: `normalized_image_count_exact`, `normalized_approachable_count_exact` | Actual ordered bass-zero triples |
| Theorem 7: actual image count 6840 | `../lean/ExactImageCounts.lean`: `Omnibus.global_image_count_exact` | Endpoints need not themselves be permitted tertian chords |
| Theorem 7: actual approachable count 2232 | `../lean/ExactImageCounts.lean`: `Omnibus.global_approachable_count_exact` | Endpoint validity is explicitly added |
| Both witnesses start unapproachably | Additional reviewer theorems in `../lean/IndependentAudit.lean` | Confirms literal `inImage = false` at both witness starts |

All six principal bound/attainment/count exports have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom inventories.

## Ordinary graph consequences and excluded claims

The strongly connected component summary, 49-edge total, and contextual approachability-restricted 7/6 bounds are consequences of the complete successor table. The paper explicitly does not label them separately exported Lean results. The whole infinite range ≤7 is an elementary consequence of the exported all-prefix theorem.

The paper does not assert that the modulo-three lower return bound, pairwise image-intersection counts, source cardinality 3240, or a first-solution/novelty claim is a checked export. It does not equate type repetition with Pyle's extension convention or settle Conjecture 1. Mixed descending/ascending walks are excluded. The 6840/2232 image counts and inverse-move membership criterion do not require any choice of sonority quotient.

## Independent replay and review

- `../verification/independent-complete-replay/INDEPENDENT_REPLAY_REPORT.md`: final PASS report
- `../verification/independent-complete-replay/SEMANTIC_REVIEW.md`: model, count meaning, quantifiers, circularity, and source-paper comparison
- `../verification/independent-complete-replay/FINAL_AUDIT.json`: 101 frozen project modules plus one reviewer audit, zero failures/cap hits/project-object reuse
- `../verification/independent-complete-replay/AXIOM_AUDIT.json`: 434 printed axiom audits across 426 declarations
- `../verification/independent-complete-replay/DEPENDENCY_LOCK.json`: exact Lean and Mathlib/dependency identity
- `../verification/independent-complete-replay/resource_receipt.json`: compiler processes and enforced limits
- `../verification/independent-complete-replay/independent_fixture_results.json`: independently reconstructed graph, types, moves, counts and witnesses

The clean replay reused installed Lean standard-library and Mathlib dependency objects. It was a clean project replay, not a compiler/Mathlib bootstrap.

## External sources and bibliographic verification

Verified publisher/arXiv pages on 13 October 2026:

- Hayden Pyle, *Generalized Omnibus Progressions: A Mathematical Formalization of Harmonic Progressions Exhibiting Semitonal Contrary Motion and Tertian Sonorities*, MusMat 9 (2025), 27–41. Publisher: https://musmat.org/journal/v9/02-Pyle.html ; PDF: https://musmat.org/journal/v9/02-Pyle.pdf ; DOI: 10.46926/musmat.2025v9.27-41. Source definitions and figures were checked against the supplied local full text (not redistributed here) and the semantic review.
- Joti Rockwell, *Birdcage Flights: A Perspective on Inter-Cardinality Voice Leading*, Music Theory Online 15(5), October 2009. https://www.mtosmt.org/issues/mto.09.15.5/mto.09.15.5.rockwell.html
- Thomas M. Fiore, Thomas Noll, Ethan Bonnell, Hayden Pyle, Noé Rodriguez, Meredith Williams, Sonia Cannas, and Moreno Andreatta, *Transformations of Triads and Seventh Chords: Group Extensions and Duality*, 2025 preprint, arXiv:2507.20811. https://arxiv.org/abs/2507.20811

The literature audit is `../PRIOR_ART_COMPARISON.md`. It reports no located matching published answer in its checked searches, not proof of priority. The paper deliberately makes no first-solution claim.

## PDF build

Run `bash build.sh` in this directory. The script configures installed TeX sources and writes only local generated support files, runs two pdfLaTeX passes, extracts text, and renders page PNGs. It neither runs Lean nor writes remotely. The final build/transcription records are archived under `../verification/paper-qa/`; running the script creates a new local `qa/` render directory.
