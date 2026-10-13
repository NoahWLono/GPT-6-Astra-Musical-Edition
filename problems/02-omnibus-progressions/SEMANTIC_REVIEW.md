# Independent omnibus semantic review

Review date: 2026-10-13. This report covers the frozen 101-module local import closure rooted at `SharpBounds`, `InfiniteRangeBound`, and `ExactImageCounts`, plus separate reviewer checks. Compilation status and resource results are recorded in the final audit report, not inferred from historical author objects.

## 1. Exact mathematical objects

A `Chord` is a four-tuple of natural numbers, with bass, tenor, alto, and soprano coordinates. Its validity predicate first requires every coordinate to lie in 0,...,11. These canonical representatives implement ordered pitch-class segments in Z/12Z; no octave register, voice spacing, root annotation, or tonal spelling is included.

The predicate then checks all 24 coordinate permutations. A permitted stacking order has either exactly one adjacent interval zero and the other two intervals in {3,4}, or has four distinct coordinates and all three adjacent intervals in {3,4}. The first condition necessarily has three distinct pitch classes with exactly one doubled. The second rejects the 4+4+4 stack because it repeats the root. The explicit permutation list contains every permutation, not merely cyclic rotations or permutations of upper voices. Thus this validity predicate matches Definitions 4–5 in the supplied Pyle paper.

A move `step v` decreases the bass by one and increases exactly the selected tenor, alto, or soprano by one, modulo 12; the other two coordinates stay fixed. This matches Definition 6. `OmnibusStep c d` additionally requires both endpoints to satisfy the chord predicate. It is a descending-only move relation; no mirror move is silently allowed.

The type `sonority c` is the sorted triple of the three upper voices' pitch-class differences from the bass. It forgets common transposition and upper-voice order while retaining bass-relative inversion and multiplicities. Its equality is an explicit modeling convention. It does not identify all inversions of a pitch-class set and does not add root-marked interpretations of symmetric sonorities.

`nodes` enumerates all sorted triples in 0,...,11 whose bass-zero realization is a valid chord. The 55-entry `checkedNodeList` is related to this intrinsic definition by twelve kernel-checked enumeration equalities and `nodes_exact`; it is not an assumed graph. Translation invariance, upper-voice permutation invariance, and canonical normalization prove that every actual valid chord projects into these nodes. `local_quotient_lift` proves exact successor semantics from every actual valid representative, in both directions.

## 2. Expanded upper-bound and attainment statements

`universal_eight_type_bound` says that for every function c from natural indices to ordered pitch-class quadruples, every n, and every initial valid chord c(0), if each of the n transitions c(k)→c(k+1), k<n, is a valid descending move, then the distinct types among c(0),...,c(n) number at most 8. This counts n+1 positions and all distinct visited types, even when the walk repeats; it is not merely a bound on simple paths.

`universal_infinite_seven_type_bound` says that when every natural-indexed transition is a valid descending move, every finite prefix c(0),...,c(N−1) has at most 7 distinct types. The empty N=0 case is included. Hence the whole infinite walk cannot contain eight distinct types: any such eight appearances would lie in one finite prefix. The older `universal_seven_prefix_bound` is the weaker pigeonhole consequence that two positions i<j≤7 have equal type.

`eight_type_bound_is_attained` provides an eight-position valid finite walk with eight distinct types. Its witness is a total function for convenience but only its first seven transitions are asserted valid. Its constant continuation is not claimed to be an infinite admissible walk.

`infinite_seven_type_bound_is_sharp` provides a genuinely infinite admissible function with seven distinct initial types. Its first chord is followed by a checked 36-state periodic ordered-chord loop. `infinite_witness_is_admissible` checks every natural-index transition by a finite-period argument, rather than assuming an infinite lift or checking only one finite prefix.

Both witnesses start at (0,0,3,6), with type (0,3,6). This chord is not in the image of a valid descending move. The witnesses therefore do not establish sharpness with an additional approachability-at-start hypothesis.

## 3. Exact count semantics

`ActualImage c` is the proposition that there exists a valid ordered source chord d and one of the three selected upper voices v such that step(v,d)=c. The target c is not required to be valid. `global_image_count_exact` asserts that this actual endpoint subtype has cardinality 6840. Different source/voice pairs yielding the same endpoint are counted once.

`global_approachable_count_exact` counts those endpoints c for which c itself is also a valid chord. This is precisely the intersection Q∩(f_T(Q)∪f_A(Q)∪f_S(Q)), and its cardinality is 2232. It does not count edges, paths, normalized types, source/voice pairs, or chord interpretations with root labels.

Although `Chord` has natural-number coordinates and is therefore infinite, the image is proved equivalent to a bounded four-coordinate encoding in `(Fin 12)^4`. Consequently the use of `Nat.card` is not hiding its zero-for-infinite-types convention. `actualImage_iff` explicitly proves boundedness plus the inverse-move membership test.

The factor 12 is proved by an explicit invertible bass normalization, then restricted to translation-invariant predicates. Bass-zero triples retain the order of all three upper voices. There is no division or multiplication by six based on an unjustified assumption of free upper permutations. The normalized counts are 570 for all endpoints and 186 for valid approachable endpoints.

The finite source list is the six upper-orderings of each independently checked canonical node. Repetitions in this raw list are allowed and harmless. `sourceRaw_membership` proves exact equality with valid bass-zero ordered chords. Normalized actual moves produce `imageRaw`; `imageRaw_membership` proves exact inverse-move membership. Deduplication then counts actual endpoints. Tenor slices are disjoint because the tenor is recovered from each element, and the equivalence to triples is proved. Alto cells similarly partition each tenor slice; all finite cell counts are kernel `decide` proofs. Accelerating literal lists are related to their intrinsic generators by definitional equalities (`rfl`), not externally supplied numerical facts.

## 4. Circularity and hidden-assumption audit

The generic closed-walk bounds assume closure and a bound on nonterminal vertices. These premises are appropriate abstract hypotheses, and the concrete theorem discharges them separately for every one of the 55 intrinsic nodes. The closure certificates recompute successors from the chord predicate, or rewrite using independently kernel-checked successor equalities. The stated 7/8 conclusions are therefore not encoded into an unproved graph premise.

The count chain imports some graph-semantic modules for convenience but does not assume the 8/7 bounds, final numerical counts, or witness sharpness. Its source-coverage and image equivalences are independently proved. The named final theorem statements contain only the intended admissibility hypotheses; exact counts and attainment theorems have no additional premises.

The complete closure was recomputed independently from source imports and matched the author's frozen manifest exactly. The fresh replay's `LEAN_PATH` contains only its new output directory plus existing Mathlib/dependency build directories. It excludes the author's project directory; no project `.olean` files were copied. No dependency directory has a colliding local project module. Standard library and Mathlib objects remain normal shared dependencies, so this is a clean project replay, not a rebuild of Lean and all of Mathlib from source.

## 5. Source-paper relation and limits

The supplied paper's Definitions 4–6 and Section V image/approachability questions support the exact cardinality interpretation above. The paper's Conjecture 1 additionally uses “sonority” and “extension” without the explicit formal equivalence/transition-event definition required to identify it with the 8/7 theorems. Its discussion also distinguishes root-marked augmented-triad interpretations. Therefore this review does not certify a proof or disproof of Conjecture 1.

The modulo-three lower endpoint, complete SCC/cycle classification, source count 3240, edge count 49, and other numerical refinements may have independent computational evidence, but they are not all named exports of the frozen three proof roots. The reviewer fixture results must not be conflated with additional Lean theorems. The separate cyclicity task is outside this audit.

No novelty claim is established. Two residual stale source comments (“Compilation is pending” in Pilot and “future compiler gate” in ClosedWalkBounds) are historical wording only; sources were intentionally left frozen. This report and the actual replay receipts govern verification status.
