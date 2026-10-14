# GPT-6 Astra Musical Edition

A public workspace for mathematical research in music theory.

**Author of all eight papers: GPT-6 Astra.** This is the requested AI-project author attribution, not an independently verified claim about the generating model's identity. This is an independent project; no official OpenAI affiliation or endorsement is claimed.

## Status

Projects 01–03 include completed results within their stated scope, checked Lean 4 proofs, LaTeX/PDF papers, independent fresh-object verification, and separately tested source-only public rebuild wrappers.

Project 02 presents **novel exact answers to the numerical image questions in Section V of Pyle (2025)**: 6840 move endpoints and 2232 approachable ordered chords. The documented literature search through 13 October 2026 located no earlier published answer; this supports the scoped novelty claim but does not certify absolute priority. Novelty remains **unconfirmed** for Projects 01, 03, 04, 05, 06, 07, and 08. Proof correctness, mathematical scope, and novelty are assessed separately.

Projects 04 and 05 add verified counterexamples, completed PDF/LaTeX papers, Lean certificates, independent audits, and source-only rebuild instructions. Their exact scopes and remaining questions are stated below.

Projects 06–08 add **finished papers proving scoped partial or conditional results**. They do not fully solve the original open problems: Project 06 leaves the intrinsic classification criterion unresolved, Project 07 leaves eventual tiling existence unresolved, and Project 08 leaves the intended scope of Pyle's conjecture unresolved. Their proofs and manuscripts are complete within the exact hypotheses stated below. The independent source rebuilds passed; separate public-wrapper replays passed for 07–08, while 06 reached a memory limit as detailed below.

## Results and research scope

### 01. Six-note one-exchange homometry

For every positive integer `n`, strict homometric six-element subsets of `Z/nZ` sharing exactly five notes exist **if and only if** `n >= 12` and (`3 | n` or `4 | n`). Here strict means that no translation or reflection identifies the two sets. The theorem concerns arbitrary pairs in this one-exchange stratum, without assuming membership in a chosen construction family.

**Novelty unconfirmed.** The polygon-plus-two-point construction has established precedents. Whether this exact all-modulus existence criterion was previously published remains unresolved. The unrestricted six-note classification in [Erickson and Jones, Problem 5.2](https://arxiv.org/html/2412.08997v4#S5) remains open here. The paper's additional order-four enumeration is proved at manuscript level and is not Lean-formalized.

- [Project overview](problems/01-six-note-homometry/README.md), [paper](problems/01-six-note-homometry/paper/one_pitch_shifts.pdf), and [LaTeX](problems/01-six-note-homometry/paper/one_pitch_shifts.tex)
- [Exact statements](problems/01-six-note-homometry/STATEMENT_INVENTORY.md) and [prior-art comparison](problems/01-six-note-homometry/PRIOR_ART_COMPARISON.md)
- [Rebuild instructions](problems/01-six-note-homometry/REBUILD.md), [independent verification](problems/01-six-note-homometry/verification/independent-replay/REPORT.md), and [public-wrapper result](problems/01-six-note-homometry/verification/public-wrapper-replay/RESULT.json)

### 02. Exact omnibus image counts and descending-walk bounds

For the ordered four-voice pitch-class chords and descending-bass maps in [Pyle (2025), Definitions 4–6](https://musmat.org/journal/v9/02-Pyle.pdf), the union of the three move images contains exactly **6840 distinct endpoints**; exactly **2232** are valid approachable ordered chords. These count actual ordered chords, retaining voice positions and repetitions. They answer the numerical questions in Section V, independently of the quotient used for the walk bounds.

**Novel exact count answers.** No earlier published answer was located in the documented search, which includes the original paper, the available author supplement and its history, exact-number searches, and discoverable related literature. Coverage is incomplete, so this is not an absolute-priority certification. The [prior-art audit](problems/02-omnibus-progressions/PRIOR_ART_COMPARISON.md) records the evidence and search limitations.

The package also proves sharp bounds of **8 distinct types for finite descending walks** and **7 for every finite prefix of infinite descending walks**, under its explicit bass-relative quotient. Both sharp witnesses begin at an unapproachable chord. No novelty claim is made for these 8/7 bounds. **Pyle's Conjecture 1 is neither solved nor disproved by this work.**

- [Project overview](problems/02-omnibus-progressions/README.md), [paper](problems/02-omnibus-progressions/paper/omnibus_bounds.pdf), and [LaTeX](problems/02-omnibus-progressions/paper/omnibus_bounds.tex)
- [Exact statements](problems/02-omnibus-progressions/STATEMENT_INVENTORY.md) and [independent semantic review](problems/02-omnibus-progressions/SEMANTIC_REVIEW.md)
- [Rebuild instructions](problems/02-omnibus-progressions/REBUILD.md), [independent verification](problems/02-omnibus-progressions/INDEPENDENT_REPLAY_REPORT.md), and [public-wrapper result](problems/02-omnibus-progressions/verification/public-wrapper-replay/RESULT.json)

### 03. Longest arithmetic progressions in golden norm scales

Let `phi = (1 + sqrt(5))/2` and `S_B = {a*phi + b > 0 : a,b in Z and |b² + a*b - a²| <= B}`. For every natural-number budget `B >= 64`, put `M = isqrt((4*B + 3) div 5)`. The exact maximum number of notes in a nonconstant arithmetic progression contained in `S_B` is

`floor((-M + sqrt(5*M² + 4*B))/2) + ceil(M*phi)`.

The theorem proves attainment, the universal upper bound, and **unit-norm step rigidity**: every maximizing increasing progression has a positive common difference of absolute algebraic norm one. The threshold 64 is sufficient; no minimal-threshold claim is made.

**Novelty unconfirmed.** The [prior-art comparison](problems/03-algebraic-tunings/PRIOR_ART_COMPARISON.md) distinguishes this exact formula and rigidity result from earlier norm-scale constructions and boundedness results. It establishes no priority. The result is specific to `S_B`; it does not optimize over arbitrary tunings or settle the broader scale-design questions in [Dettmann and Taylor-West, *Algebraic tunings*](https://people.maths.bris.ac.uk/~macpd/music/Algebraic_tunings.pdf).

- [Project overview](problems/03-algebraic-tunings/README.md), [paper](problems/03-algebraic-tunings/paper/golden_progressions.pdf), and [LaTeX](problems/03-algebraic-tunings/paper/golden_progressions.tex)
- [Exact statements](problems/03-algebraic-tunings/STATEMENT_INVENTORY.md)
- [Rebuild instructions](problems/03-algebraic-tunings/REBUILD.md), [independent verification](problems/03-algebraic-tunings/verification/independent-replay/INDEPENDENT_AUDIT.md), and [public-wrapper result](problems/03-algebraic-tunings/verification/public-wrapper-replay/RESULT.json)

### 04. Counterexamples to Yust's two folding conjectures

Both arbitrary-cardinality folding characterizations in Yust's 2022 paper fail under the paper's stated definitions. The pitch-space example is the seven-note pair `{0,1,2,3,6,7,9}` and `{0,1,2,3,6,8,9}`. The pitch-class example in `Z/12Z` is `{0,1,3,4,6}` and `{0,1,3,4,7}`. Each pair has two distinct shared codimension-one T/I subset types and all but one interval occurrence in common, yet no permitted single folding (or T-shift in the pitch-class case) relates the whole-set types.

The Lean certificate checks both concrete counterexamples, including arbitrary source and target transposition/inversion representatives. An infinite seven-note family is proved in the manuscript, **not Lean-formalized**. The work does not contradict the proved tetrachordal proposition, classify all exceptions, or address connectivity by sequences of operations. **Novelty unconfirmed.**

- [Project overview](problems/04-yust-folding-counterexamples/README.md), [paper](problems/04-yust-folding-counterexamples/output/pdf/yust_folding_counterexamples.pdf), and [LaTeX](problems/04-yust-folding-counterexamples/paper/yust_folding_counterexamples.tex)
- [Mathematical account and prior-art limits](problems/04-yust-folding-counterexamples/RESEARCH_NOTE.md), [Lean certificate](problems/04-yust-folding-counterexamples/formal/Counterexamples.lean), and [independent audit](problems/04-yust-folding-counterexamples/audit/SEMANTIC_AUDIT.md)
- [Rebuild instructions](problems/04-yust-folding-counterexamples/REBUILD.md) and [audit receipt](problems/04-yust-folding-counterexamples/audit/receipt.json)

### 05. Endpoint counterexamples to the printed Erdős-deep triple classification

Primitive families in `Z/34Z` with generators `(1,6,12)` and lengths `(10,9,5)`, and in `Z/48Z` with generators `(1,6,18)` and lengths `(20,5,5)`, are Erdős-deep although their length triples are absent from the printed fifteen-triple list in Dukes–Gaede's 2023 Conjecture 1. Every constituent separately is Erdős-deep; the families have positive distance multiplicities exactly `1,…,13` and `1,…,20`, respectively.

These counterexamples use the endpoint convention `k <= floor(order(g)/2)+1`. They **do not refute the stricter variant** requiring `k <= floor(order(g)/2)` for every constituent. The thesis's printed p. 43 pseudocode explicitly bounds only the largest constituent length; both examples satisfy that bound, so no cause of the historical search omission is claimed. The paper does not prove a repaired classification. **Novelty unconfirmed.**

- [Project overview](problems/05-erdos-deep-counterexamples/README.md), [paper](problems/05-erdos-deep-counterexamples/paper/erdos_deep_counterexamples.pdf), and [LaTeX](problems/05-erdos-deep-counterexamples/paper/erdos_deep_counterexamples.tex)
- [Exact results](problems/05-erdos-deep-counterexamples/RESULT.md), [Lean certificate](problems/05-erdos-deep-counterexamples/ErdosDeepCounterexamples.lean), [source reconciliation](problems/05-erdos-deep-counterexamples/source-audit.md), and [prior-art limits](problems/05-erdos-deep-counterexamples/prior-art-check.md)
- [Rebuild instructions](problems/05-erdos-deep-counterexamples/REBUILD.md), [independent audit](problems/05-erdos-deep-counterexamples/independent-audit/AUDIT.md), and [verification receipt](problems/05-erdos-deep-counterexamples/verification-receipt.json)

### 06. Collision blocks and certified difference-table maximality

The package proves that 22 explicit five-point difference-table loci are nonempty, pairwise distinct, and maximal against every competing edge permutation in their respective fixed canonical chambers. The representatives and their count are already known from Erickson–Jones. A general collision criterion reduces global maximality verification to 97 fiber-permutation choices across the 22 cases, with at most 32 for a single case.

This is a **finished structural partial-result paper**, not a new 22-case classification or a solution of Problem 5.1. It does not supply an intrinsic combinatorial selection rule or prove completeness of the list. **Novelty unestablished.**

- [Project overview](problems/06-difference-table-maximality/README.md), [paper](problems/06-difference-table-maximality/paper/difference-table-structural-partial.pdf), and [LaTeX](problems/06-difference-table-maximality/paper/difference-table-structural-partial.tex)
- [Exact statements](problems/06-difference-table-maximality/STATEMENTS.md), [independent audit](problems/06-difference-table-maximality/verification/INDEPENDENT_AUDIT.md), and [source/novelty limits](problems/06-difference-table-maximality/SOURCES_AND_LIMITS.md)
- [Rebuild instructions](problems/06-difference-table-maximality/REBUILD.md) and [public-package replay](problems/06-difference-table-maximality/verification/PUBLIC_REPLAY.json)

### 07. A variance bound for transverse rhythmic triplets and monochromatic queens

A same-color nonattacking placement of `t` queens on a `k × k` board satisfies `t² - 1 <= 3k(k - t)`. The same bound holds for transverse triplets in actual exact-cover rhythmic tilings by three-term arithmetic progressions with positive, pairwise distinct gaps. The formal proof includes the zero-triplet case and bridges the numerical estimate to the actual tiling objects.

This is a **finished supporting-bound paper**. The original eventual-existence question for perfect rhythmic triplet tilings remains unresolved. The asymptotic and square-root reformulations are manuscript-level corollaries. **Novelty unestablished.**

- [Project overview](problems/07-rhythmic-tiling-bound/README.md), [paper](problems/07-rhythmic-tiling-bound/paper/transverse-bound.pdf), and [LaTeX](problems/07-rhythmic-tiling-bound/paper/transverse-bound.tex)
- [Exact statements](problems/07-rhythmic-tiling-bound/STATEMENTS.md), [independent audit](problems/07-rhythmic-tiling-bound/verification/INDEPENDENT_AUDIT.md), and [source/novelty limits](problems/07-rhythmic-tiling-bound/SOURCES_AND_LIMITS.md)
- [Rebuild instructions](problems/07-rhythmic-tiling-bound/REBUILD.md) and [public-package replay](problems/07-rhythmic-tiling-bound/verification/PUBLIC_REPLAY.json)

### 08. A conditional root-marked three-to-six omnibus bound

For every infinite admissible walk of actual ordered four-voice chords using only bass-down moves, with a valid admissible predecessor of its initial chord, every valid choice of root reading has an entire quality/inversion range of cardinality between three and six, modulo transposition. The endpoints are attained. A seven-type prefix from an initial chord without an admissible predecessor demonstrates the importance of that hypothesis.

This is a **finished conditional-theorem paper**. It does not establish that its explicit hypotheses and counted labels coincide with the intended full wording of Pyle's Conjecture 1, and is not an unqualified resolution of that conjecture. The interpretation question remains open in the appendix. Mixed-direction walks are outside the theorem. **Novelty unestablished.**

- [Project overview](problems/08-pyle-conditional-bound/README.md), [paper](problems/08-pyle-conditional-bound/paper/root_marked_omnibus.pdf), and [LaTeX](problems/08-pyle-conditional-bound/paper/root_marked_omnibus.tex)
- [Exact statements](problems/08-pyle-conditional-bound/STATEMENTS.md), [independent audit](problems/08-pyle-conditional-bound/verification/INDEPENDENT_AUDIT.md), and [source reuse/limits](problems/08-pyle-conditional-bound/SOURCES_AND_LIMITS.md)
- [Rebuild instructions](problems/08-pyle-conditional-bound/REBUILD.md) and [public-package replay](problems/08-pyle-conditional-bound/verification/PUBLIC_REPLAY.json)

## Verification and trust boundary

For Projects 01–03, the independent replays and the separate public-wrapper replays all passed:

- Project 01: 33 project modules and one independent exact-statement fixture
- Project 02: 101 project modules and one independent reviewer module
- Project 03: 18 project modules and two independent fixtures

Each replay compiled the complete frozen project source closure into fresh project objects, with zero project-object reuse. The pinned Lean compiler, standard-library, Mathlib, and package objects remain trusted dependencies; they were not themselves rebuilt from source. The common baseline is Lean `4.32.2` and Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`.

For Projects 01–03, the formal claims are the declarations identified in each statement inventory. Computational checks and manuscript-only deductions are identified separately. Historical development comments and incomplete attempts are retained as provenance where applicable; the final verification records establish the completed replay status. See each project's independent report and public-wrapper result above for the distinct runs and their limits.

Projects 04 and 05 each include a separate fresh-object audit of their single Lean module, exact export/axiom checks, and independent mathematical or actual-point counting checks. Their audit reports specify the trust boundary and the precise frozen sources. The publication wrappers also compile those source files into fresh temporary objects; their receipts are in each project's `publication-check/` folder. The infinite family in Project 04 and bounded searches in both projects are not additional Lean theorems.

Projects 06–08 include complete frozen source closures, exact export/axiom checks, completed independent source rebuild evidence, and separately recorded public-wrapper replay attempts:

- Project 06: 20 project modules plus two audit fixtures
- Project 07: five project modules plus one audit fixture
- Project 08: 28 project modules plus two audit fixtures

For 07 and 08, the public-wrapper replays passed completely. For 06, the new wrapper replay completed 14 modules and then reached a 6 GiB resident-memory cutoff in CompactGlobalB6; it is explicitly marked INCOMPLETE. Its original independent fresh rebuild passed all 20 project modules plus the aggregate and export checks, and all frozen source hashes and recorded successful object hashes were revalidated before publication. Project 06 relies on that completed independent audit, without claiming a full pass of the new wrapper.

The independent rebuilds and public-wrapper attempts use fresh project objects and the same pinned Lean/Mathlib baseline. Standard compiler, library, Mathlib, and package objects are trusted and reused. The exported theorem dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`. The reports distinguish formal claims, manuscript deductions, semantic interpretation, and novelty. Public packages contain mathematical reports and sanitized receipts, without raw diagnostic logs or machine-specific build metadata.

The root `SHA256SUMS` is retained unchanged as the manifest of the original Projects 01–03 release; its README hash belongs to that release. Current integrity manifests for Projects 04–08 are [04/SHA256SUMS](problems/04-yust-folding-counterexamples/SHA256SUMS), [05/SHA256SUMS](problems/05-erdos-deep-counterexamples/SHA256SUMS), [06/SHA256SUMS](problems/06-difference-table-maximality/SHA256SUMS), [07/SHA256SUMS](problems/07-rhythmic-tiling-bound/SHA256SUMS), and [08/SHA256SUMS](problems/08-pyle-conditional-bound/SHA256SUMS). Run each from its own project folder.

## Research workflow and organization

Each numbered folder under `problems/` contains:

- A precise problem statement, definitions, assumptions, and source references
- Reproducible computations where useful, distinguished from proof certificates
- Lean 4 formalizations, proof-checking evidence, pinned dependencies, and source checksums
- LaTeX source and a corresponding PDF write-up
- Prior-art comparisons documenting the scope and limits of novelty claims

Sheet music or musical notation may be added where it helps explain a result. Future research and additional proof/write-up files will be added under the same numbered organization.

