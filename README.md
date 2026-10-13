# GPT-6 Astra Musical Edition

A public workspace for mathematical research in music theory.

**Author of all three papers: GPT-6 Astra.** This is the requested AI-project author attribution, not an independently verified claim about the generating model's identity. This is an independent project; no official OpenAI affiliation or endorsement is claimed.

## Status

All three projects now include completed results within their stated scope, checked Lean 4 proofs, LaTeX/PDF papers, independent fresh-object verification, and separately tested source-only public rebuild wrappers.

Project 02 presents **novel exact answers to the numerical image questions in Section V of Pyle (2025)**: 6840 move endpoints and 2232 approachable ordered chords. The documented literature search through 13 October 2026 located no earlier published answer; this supports the scoped novelty claim but does not certify absolute priority. Novelty remains **unconfirmed** for Projects 01 and 03. Proof correctness, mathematical scope, and novelty are assessed separately.

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

## Verification and trust boundary

The independent replays and the separate public-wrapper replays all passed:

- Project 01: 33 project modules and one independent exact-statement fixture
- Project 02: 101 project modules and one independent reviewer module
- Project 03: 18 project modules and two independent fixtures

Each replay compiled the complete frozen project source closure into fresh project objects, with zero project-object reuse. The pinned Lean compiler, standard-library, Mathlib, and package objects remain trusted dependencies; they were not themselves rebuilt from source. The common baseline is Lean `4.32.2` and Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`.

The formal claims are the declarations identified in each statement inventory. Computational checks and manuscript-only deductions are identified separately. Historical development comments and incomplete attempts are retained as provenance where applicable; the final verification records establish the completed replay status. See each project's independent report and public-wrapper result above for the distinct runs and their limits.

## Research workflow and organization

Each numbered folder under `problems/` contains:

- A precise problem statement, definitions, assumptions, and source references
- Reproducible computations where useful, distinguished from proof certificates
- Lean 4 formalizations, proof-checking evidence, pinned dependencies, and source checksums
- LaTeX source and a corresponding PDF write-up
- Prior-art comparisons documenting the scope and limits of novelty claims

Sheet music or musical notation may be added where it helps explain a result. Future research and additional proof/write-up files will be added under the same numbered organization.
