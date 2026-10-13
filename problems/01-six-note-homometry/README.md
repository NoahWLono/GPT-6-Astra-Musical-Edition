# Project 01: Six-note one-exchange homometry

For every positive integer `n`, there are six-element subsets `A, B` of
`Z/nZ` with exactly five shared elements, identical directed-difference
multiplicities, and no translation or reflection taking `A` to `B` **if and
only if**

> `n >= 12` and (`3` divides `n` or `4` divides `n`).

This is the **one-exchange existence theorem**, not a complete classification
of six-note homometric sets or of their homometry classes.

- [Six-page paper](paper/one_pitch_shifts.pdf) and [editable LaTeX](paper/one_pitch_shifts.tex)
- [Exact statements and verification scope](STATEMENT_INVENTORY.md)
- [Prior art and unresolved novelty](PRIOR_ART_COMPARISON.md)
- [Source-only rebuild instructions](REBUILD.md)
- [Independent verification report](verification/independent-replay/REPORT.md)
- [Independent verification result](verification/independent-replay/verification.json)

## Formal verification

`OnePitchShift.six_note_one_exchange_existence_iff` is proved with only the
ambient assumption `[NeZero n]`. Its left side quantifies over arbitrary finite
sets with intersection five; it does not assume normalized representatives or
membership in a chosen construction family. Simultaneous translation into and
out of the normalized form is proved.

All **33 project modules and one independent exact-statement fixture** passed
an independent fresh-object replay after source freeze. The fixture
`IndependentHomometryAudit.positive_modulus_exact_statement` uses an explicit
`0 < n` hypothesis and expands both homometry and dihedral equivalence into
elementary finite-set expressions. No project-specific predicate remains in
its statement.

The final theorem and fixture use only `propext`, `Classical.choice`, and
`Quot.sound`. Their frozen proof-source bytes are preserved here unchanged.
Historical status comments and the original freeze manifest describe earlier
stages; the later independent PASS receipts establish the checked status.

The pinned baseline is Lean 4.32.2 and Mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c`. Project objects were rebuilt;
standard-library and Mathlib/package objects were reused and remain trusted.
Compiler plus separately recorded import-scan CPU was 115.579767 seconds.

The packaged source-only public wrapper also passed all 34 fresh compilations
with zero project-object reuse and all 13 expected named axiom audits, using
86.060723 actual aggregate CPU seconds. Its [result](verification/public-wrapper-replay/RESULT.json)
and [resource summary](verification/PUBLIC_WRAPPER_REPLAY.json) are separate
from the historical independent replay. No failure or resource cap occurred.

## What the paper additionally contains

The paper gives a mathematical proof and independent audit of an order-four
quotient count: for `n = 8s`, the number of unordered pairs of distinct bracelet
classes admitting an order-four one-exchange realization is `2 floor(s/2)`;
it is zero when `8` does not divide `n`. **That separate enumeration theorem is
not Lean-formalized.** Bounded computations are checks, not proof certificates.
The four structural templates are exhaustive candidates and still require a
dihedral-inequivalence test in general.

The polygon-plus-two-point construction is established prior art, attributed
to Patterson (1944) through Goyette's dissertation. The original Patterson
page has not been directly inspected. Whether the exact all-modulus six-note
existence criterion was previously published remains unresolved. No novelty
or priority claim is made.

## Files

`lean/` contains 34 frozen sources. `reproducibility/` records their hashes,
the replay order, the exact compiler pin, and the full Mathlib dependency lock.
`verification/independent-replay/` preserves the original audit and receipts,
including historical cloud-workspace paths. Those paths are provenance, not
installation requirements. Compiled project objects and local exploratory
work are not distributed.
