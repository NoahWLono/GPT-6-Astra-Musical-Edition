# Golden norm-scale statement inventory

## Comparison class
`GoldenAP phi (B : ℤ) n` consists of integer coordinates `a,b,c,d`,
positive evaluated start and step, and the actual norm inequalities
`|goldenNorm (a+j*c) (b+j*d)| ≤ B` for each natural `j ≤ n`.
Here `n` is the number of gaps; the number of notes is `n+1`.
No continuous bound, normalized-sample condition, or unit-step condition is
included in this structure.

## Verified results
See exact receipts and axiom audit files for the checked source hashes.
- Nonzero integer coordinates have nonzero golden norm.
- Every actual AP satisfies the explicit real square-root global span bound.
- A unit step can be normalized to step 1 with integer coordinates and all
  original norm bounds preserved.
- The integer quadratic minimum and fixed-line count upper bound are checked.
- `goldenCanonicalRun` constructs an actual AP from the depth threshold and
  endpoint count; all individual norm bounds are derived, not postulated.

## Final target, compiled and axiom-audited
`golden_exact_maximum (B : ℕ) (hB : 64 ≤ B)`.
Its budget inside `GoldenAP` is the explicit cast `(B : ℤ)`.
The conclusion is the conjunction of:
1. An actual AP attains `goldenMaximumLength B` notes.
2. Every actual AP has at most that many notes.
3. Every AP attaining that count has absolute step norm one.

`goldenMaximumLength` uses the integer index
`Nat.sqrt ((4*B+3)/5)` and the real square root of `5*M²+4*B`.
`goldenMaximumLength_formula` expresses the count as
`floor((-M+sqrt(5*M²+4*B))/2) + ceil(M*goldenPhi)`.

The generic assembly has integer parameters `(B M : ℤ)` with `64 ≤ B`,
nonnegative M, depth(M) ≤ B and B < depth(M+1). It temporarily accepts an
abstract nonnegative square-root operation. The final wrapper supplies
`Real.sqrt` and proves the threshold conditions. These generic root/threshold
premises are absent from the final target statement.

The complete theorem and all dependencies passed their bounded Lean gates.
The independent fresh-object replay then passed all 18 frozen project modules
and two independent fixtures with zero project-object reuse. The fixture
`IndependentGoldenAudit.nonconstant_attainment` separately proves an attaining
witness with at least two notes. Some frozen proof comments retain historical
development status; the final replay records supersede those comments. All
public proof sources preserve the independently replayed bytes exactly.

No arbitrary-real budget theorem is asserted. No comparison across arbitrary
scales with equal notes-per-octave is asserted. This is an exact extremal
problem within the positive bounded-norm golden scale.
