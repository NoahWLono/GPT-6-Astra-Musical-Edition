# Independent audit and fresh-object replay: golden norm-scale maximum

Date: 13 October 2026.

## Verdict

**PASS.** The final result `AlgebraicTunings.golden_exact_maximum` proves the manuscript's exact maximum formula, attainment, and norm-one rigidity for natural-number budgets `B ≥ 64`. Every reachable project module was recompiled into a fresh object directory. Two independently written fixtures also passed. No mathematical gap or hypothesis/conclusion mismatch was found in these claims.

This is verification of a specified bounded-norm scale. It neither solves optimization over all tunings nor establishes novelty or priority.

## Exact statement checked

Let `phi = (1 + sqrt(5))/2`, and set

- `N(a*phi+b) = b*b + a*b - a*a` for integer `a,b`;
- `S_B = {a*phi+b > 0 : a,b are integers and |N(a*phi+b)| ≤ B}`;
- `M = isqrt((4*B+3) div 5)`;
- `F = floor((-M + sqrt(5*M*M+4*B))/2) + ceil(M*phi)`.

For each `B : Nat` with `64 ≤ B`, the target proves all three statements:

1. An actual progression has exactly `F` notes.
2. Every actual progression has at most `F` notes.
3. Every progression with `F` notes has common-difference norm of absolute value one.

Here an actual progression is `GoldenAP goldenPhi (B : Int) n`. It has integer coordinates `a,b,c,d`, a strictly positive evaluated start `a*phi+b`, a strictly positive evaluated step `c*phi+d`, and the inequality

`|N((a+j*c)*phi + b+j*d)| ≤ B`

for **every** natural `j ≤ n`. Thus `n` counts gaps and `n+1` counts notes. The structure does not assume the desired upper bound, unit norm, normalization, or a continuous interpolation bound. Positive start and step imply positivity of every represented note. An ordinary nonconstant increasing progression in `S_B` has exactly this representation: its start and the difference of its first two terms lie in `Z[phi]`. Decreasing progressions can be reversed.

The structure permits `n=0`. This harmless representation detail does not weaken attainment: `IndependentGoldenAudit.nonconstant_attainment` was separately checked and proves an attaining witness with `1 ≤ n`. It uses the valid two-note progression `1,2`, the universal bound, and attainment. The positive step then makes the attained notes distinct.

`IndependentGoldenAudit.exact_statement` states the full conjunction with explicit real square root, explicit natural integer-square-root threshold, and explicit floor-plus-ceiling formula. Its proof checks that the target is definitionally/rewrite-equivalent to this independent statement.

## Formula and threshold alignment

The final theorem has only the premises `B : Nat` and `64 ≤ B`. Its scale budget is explicitly `(B : Int)`.

The manuscript defines `M` as the largest nonnegative integer satisfying `floor(5*M*M/4) ≤ B`. The source proves both the depth inequality at `M` and the strict inequality at `M+1`, together with depth monotonicity. Its executable threshold `Nat.sqrt ((4*B+3)/5)` is therefore precisely the manuscript threshold. Integer division is intentional, and `M ≥ 0` is proved.

The count initially uses `floor((-M+r)/2) - floor(-M*phi)`. `goldenMaximumLength_formula` proves the floor-plus-ceiling identity. This handles the strict positive lower endpoint correctly, with no off-by-one assumption about irrationality.

The generic assembly temporarily abstracts nonnegative square roots and the threshold. The final wrapper supplies `Real.sqrt`, proves its defining equations at all required nonnegative arguments, and supplies the proved threshold conditions. Those abstractions are not additional premises of the final target.

## Source proof audit

The complete proof chain was read, rather than inferred from theorem names or author receipts:

- The integer norm is the product of the two real embeddings. Nonzero integer coordinates have nonzero norm, so an actual positive step has positive absolute integer norm.
- The exact monic-quadratic interpolation identity derives a continuous bound from all actual integer samples. Positivity is used in the sharp interval-span bound. This establishes the universal `n ≤ (1+sqrt(2))*sqrt(B/|N(d)|+1/4)` estimate.
- Explicit integer coordinate formulas normalize every norm-one positive step to step one while preserving every note's absolute norm and positivity.
- The exact discrete vertex minimum is `-floor(5*m*m/4)`, including odd and even coefficients. At and below the threshold the canonical run attains the exact floor count.
- The quantitative lower construction is derived with algebraic root-gap inequalities, rather than assumed. Together with the universal bound it excludes all steps with absolute norm at least two.
- The normalized-line cases are exhaustive: `m ≤ 0`; `0 < m ≤ M`; and `m > M`. The first case is too short. Exact integer endpoint monotonicity handles the second. A forbidden integer nearest the vertex separates the third; the formal proof derives the stronger squared-span estimate `n*n ≤ 2*B` directly from discrete endpoints.
- The generic assembly proves both global maximality and every-maximizer rigidity, and the final wrapper removes all intermediate abstract parameters.

No reachable project source contains `sorry`, `admit`, a custom `axiom` declaration, or `native_decide` outside comments. The final named axiom audits also exclude hidden custom assumptions.

## Independent replay provenance

Frozen author manifest SHA256:

`1070d311cb04ff5c2641f3a0fd2a5bd3ef42bd7e6b369f92538f80e500747797`

The complete local import closure was derived independently from the source, checked for cycles, compared with the author manifest and order, and found to contain exactly these 18 modules:

1. GoldenNormCore
2. GoldenIntervals
3. GoldenNonzero
4. GoldenAPInterface
5. GoldenUnitNormalization
6. GoldenStepMinimum
7. GoldenCounting
8. GoldenAttainment
9. GoldenLowerEstimate
10. GoldenCountMonotonic
11. GoldenRigidity
12. GoldenSplitBound
13. GoldenNonpositiveLine
14. GoldenThreshold
15. GoldenExactGeneric
16. GoldenThresholdIndex
17. GoldenRealBound
18. GoldenExact

Every copied source matched its frozen SHA256. Independently removing block comments confirmed equality of all noncomment bytes with the original checked source snapshots. Six stale comments were the only author changes before the freeze. Reference objects in the author manifest predate those comment edits; they were **not** imported or treated as fresh replay evidence.

Toolchain:

- Lean 4.32.2, release commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- Lean binary SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`; tracked worktree clean.
- The frozen `lean-toolchain` and `lake-manifest.json` hashes matched.
- All 14 distinct direct external imports resolved uniquely, and their reused object hashes were recorded in `preflight.json`.

`LEAN_PATH` contained the fresh `independent-replay/objects` directory and pinned Mathlib/package object directories only. The original project object directory was absent. Compilation ran from copied source files in `independent-replay/sources` with `-j1`.

Trust boundary: the entire reachable **project** closure was rebuilt; Lean and existing Mathlib/package caches were reused. This is not a from-scratch reconstruction of Mathlib or the compiler.

## Resource results and axioms

All 18 modules and both fixtures passed on their first compiler invocation in this independent replay.

- Actual aggregate child CPU: **78.945011 seconds**.
- Sum of per-process wall times: **79.155032 seconds**.
- Maximum sampled RSS: **2,125,451,264 bytes**, below 2 GiB.
- Named axiom audit occurrences: **67**; all standard-only or empty. This count includes repeated final-target audits, not 67 distinct project theorems.
- No CPU, wall, RSS, output, or disk-floor cap was hit.
- Compiler slot released after completion.

The target, formula theorem, explicit statement fixture, and nonconstant-attainment fixture each depend only on:

`propext`, `Classical.choice`, `Quot.sound`.

The enforced limits were a 19.5-second observed CPU watchdog / 20-second hard CPU limit per process, 35-second wall limit per process, 2-GiB sampled RSS, 64-MiB output, 4-GiB free-disk floor, and 180-second aggregate actual child CPU budget.

The logs include benign unused-binder warnings. There are no failed compilations or sorry warnings.

## Precise limitations

- The target covers integer budgets at least 64. It is not an arbitrary-real-budget theorem or an all-small-budget formula.
- “Unit common difference” means a positive algebraic unit, equivalently absolute norm one. It does not mean every original progression literally has numerical common difference one; that is obtained after unit normalization.
- No uniqueness of the maximizing normalized coefficient or progression is claimed.
- The asymptotic corollary and `L(20)=11` remain manuscript-level deductions from checked ingredients unless separately packaged as Lean theorems. They are not conjuncts of `golden_exact_maximum`.
- No theorem about optimality among all tunings of equal pitch density, total three-term-progression counts, or other quadratic orders is covered by this replay.
- Formal correctness does not certify novelty or publication priority.

## Prior-art scope checked

I independently reopened the primary sources. Dombek–Hajdu–Pethő, *Representing algebraic integers as linear combinations of units*, Theorem 2.2 on page 4, already bounds nonconstant AP length in fixed-fold sums of bounded-absolute-norm algebraic integers. Taking one summand covers boundedness for this scale before imposing positivity:

https://arato.inf.unideb.hu/petho.attila/cikkek/dhpnew6rev.pdf

Dettmann–Taylor-West, *Algebraic tunings*, defines the positive bounded-norm scale in Section 4 and discusses the problem of maximizing arithmetic-sequence counts over pitch-class choices in Section 5. Its displayed long example contains nine notes; it does not establish a longest-progression optimum. Those original scale-design questions have a different objective/comparison class from this exact maximum theorem:

https://people.maths.bris.ac.uk/~macpd/music/Algebraic_tunings.pdf

Elsholtz–Frei concerns progressions in represented norm-form values, another distinct extremal problem:

https://arxiv.org/abs/1810.11251

A small targeted search did not locate the exact formula being verified. That search is not an exhaustive novelty audit. The exact eventual formula and extremal unit-step rigidity may be contributions, but the defensible status is **candidate new result; priority not established**.

## Evidence files

- `RESULT.json`: final machine-readable result.
- `preflight.json`: source/import/hash and external-cache checks.
- `author-manifest.json`: immutable copy of the frozen author manifest.
- `replay-ledger.json`: all 20 compiler invocation receipts, exact commands, hashes, limits, timings, and named axiom outputs.
- `sources/IndependentGoldenFixture.lean`: independently expanded full statement.
- `sources/IndependentGoldenNonconstantFixture.lean`: nonconstant attainment check.
- `logs/*.log` and `logs/*.receipt.json`: per-module evidence.
- `prepare_replay.py`, `run_replay.py`, `run_nonconstant_fixture.py`: preparation and bounded execution scripts.
