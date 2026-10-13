# 03 Longest arithmetic progressions in golden norm scales

This project gives a checked exact formula for a specified golden norm-scale
problem. It is project **03** in the music research sequence: 01 homometric
chords, 02 omnibus sonorities, 03 algebraic tunings.

**Status:** the complete theorem, all 18 project modules, and two independent
fixtures passed a fresh-object replay. Originality is unconfirmed. This folder
is a local publication candidate; no publication is implied by its existence.

## Exact result and comparison class

Let `phi = (1 + sqrt(5))/2` and

`S_B = {a*phi + b > 0 : a,b in Z and |b² + a*b - a²| <= B}`.

For each natural-number budget `B >= 64`, define

`M = isqrt((4*B + 3) div 5)`.

Equivalently, `M` is the largest nonnegative integer with
`floor(5*M²/4) <= B`. The exact maximum number of notes in a nonconstant
arithmetic progression contained in `S_B` is

`floor((-M + sqrt(5*M² + 4*B))/2) + ceil(M*phi)`.

The theorem proves all three parts:

1. This count is attained by an actual progression.
2. Every progression in the defined class has at most this count.
3. Every maximizing progression has a positive common difference of absolute
   algebraic norm one.

The final Lean declaration is
[`AlgebraicTunings.golden_exact_maximum`](lean/GoldenExact.lean), with only
`B : Nat` and `64 <= B` as its premises. Its formula is expanded by
`goldenMaximumLength_formula` and independently restated in
[`IndependentGoldenFixture.lean`](lean/IndependentGoldenFixture.lean).
[`IndependentGoldenNonconstantFixture.lean`](lean/IndependentGoldenNonconstantFixture.lean)
checks that attainment really gives at least two distinct notes.

`GoldenAP` records integer coordinates, strictly positive start and step, and
the actual norm bound at every note. It does not assume normalization,
unit norm, a continuous bound, or the desired length bound. Its parameter `n`
counts gaps, so a represented progression has `n+1` notes. An ordinary
increasing progression with at least two notes in `S_B` has this representation;
a decreasing progression can be reversed. See the
[statement inventory](STATEMENT_INVENTORY.md) and
[independent audit](verification/independent-replay/INDEPENDENT_AUDIT.md).

## Scope and prior art

This solves the longest-progression problem **inside the particular family
`S_B`**. It does not optimize over all tunings at a fixed pitch density, maximize
the total number of three-term progressions, or solve the broader scale-design
questions in Dettmann and Taylor-West's *Algebraic tunings*.

The norm-scale construction and musical motivation come from
[Dettmann and Taylor-West](https://doi.org/10.1080/17459737.2023.2234126).
Effective boundedness of progression length in bounded-norm algebraic integers
was already known from Dombek, Hajdu, and Pethő, Theorem 2.2 of
[*Representing algebraic integers as linear combinations of units*](https://arato.inf.unideb.hu/petho.attila/cikkek/dhpnew6rev.pdf).
The candidate contribution is the exact eventual formula, its sharp leading
constant under positivity, and the every-maximizer unit-norm conclusion.

A bounded review found no matching exact formula in the inspected primary
sources or searches. It did not establish originality or priority. The
[prior-art comparison](PRIOR_ART_COMPARISON.md) records sources, distinctions,
access gaps, and unresolved literature questions. No “first” or globally
optimal-tuning claim is made.

The manuscript also proves `L(20)=11` and the asymptotic leading term
`(1+sqrt(2))*sqrt(B)`. These are manuscript-level deductions from checked
ingredients; they are not separately packaged Lean theorems or conjuncts of
`golden_exact_maximum`. The threshold 64 is sufficient, not claimed minimal.
No arbitrary-real-budget theorem, uniqueness of maximizers, or theorem for
other quadratic orders is asserted.

## Verification status

The recorded independent replay compiled all **18 project modules and both
independent fixtures** from frozen sources into initially empty project-object
storage. All 20 compilations passed with **zero project-object reuse** and
**78.945011 aggregate child CPU seconds**. The reported 67 named axiom-audit
occurrences include repeated target audits; they are not 67 distinct theorems.

The target, formula theorem, and both fixtures use only `propext`,
`Classical.choice`, and `Quot.sound`. The source scan found no `sorry`, `admit`,
custom `axiom`, or `native_decide` outside comments. The
[final result](verification/independent-replay/RESULT.json),
[20-invocation ledger](verification/independent-replay/replay-ledger.json),
[logs and receipts](verification/independent-replay/logs/), and
[source checksums](SOURCE_SHA256SUMS) are included.

The trust boundary is explicit: the full **project** closure was rebuilt;
the pinned Lean compiler and existing Mathlib/package objects were reused.
Mathlib and Lean were not reconstructed from source. Historical comments in
some frozen Lean files still describe earlier development stages. The final
replay records supersede those comments; the proof bytes are preserved exactly.

The packaged public [`rebuild.py`](rebuild.py) wrapper subsequently passed its
own second fresh-object replay of all 20 sources, using **85.271496 aggregate
child CPU seconds**, with zero project-object reuse and no resource-cap hits.
The same four final axiom audits passed. See the
[public-wrapper result](verification/public-wrapper-replay/RESULT.json),
[ledger](verification/public-wrapper-replay/replay-ledger.json), and
[summary](verification/PUBLIC_WRAPPER_REPLAY_SUMMARY.json). The compiler and
dependency acquisition steps were not rebuilt or rerun as part of that replay.

## Files

- [`paper/golden_progressions.pdf`](paper/golden_progressions.pdf): manuscript
- [`paper/golden_progressions.tex`](paper/golden_progressions.tex): editable LaTeX
- [`lean/`](lean/): the complete 20-file frozen source closure, including fixtures
- [`reproducibility/`](reproducibility/): toolchain, Mathlib, dependency, and order locks
- [`verification/`](verification/): preserved independent replay evidence and packaging checks
- [`computations/`](computations/): optional integer-only regression scripts and recorded outputs

No project `.olean` or other compiled project object is distributed.

## Source-only rebuild

See [REBUILD.md](REBUILD.md) for dependency preparation and commands. The
wrapper runs the 20 modules in the frozen topological order with `-j1`, copies
only source into a new workspace, refuses an existing output directory, and
uses fresh project objects plus pinned Mathlib/package objects as `LEAN_PATH`.

The expected environment is Linux x86_64, Python 3.10 or later, git, Lean
`4.32.2` (release commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`), and Mathlib
commit `905b95818eb32af7874a58b427f50c1711a5e96c`. Full hashes and all eight
dependency revisions are in the bundled locks.
