# Statement inventory and scope

## Main checked theorem

`OnePitchShift.six_note_one_exchange_existence_iff`, in
[`lean/FullSixNoteExistence.lean`](lean/FullSixNoteExistence.lean), states:

For `n : Nat` with `[NeZero n]`, there exist `A B : Finset (ZMod n)` such that
`A.card = 6`, `B.card = 6`, `(A ∩ B).card = 5`, `Homometric A B`, and
`not DihedralEquivalent A B`, if and only if
`12 <= n` and (`3` divides `n` or `4` divides `n`).

Homometry means equality, for every `t`, of the integer sum over `x` in the
set of the indicator that `x - t` is in the set. This counts precisely the
ordered pairs of difference `t`. Dihedral equivalence includes all
translations `x -> x + t` and all translated reflections `x -> t - x`.

The existence quantifier is unrestricted apart from the displayed conditions.
The proof does not assume that a witness belongs to a named parametric family.

## Independent statement fixture

[`lean/IndependentExactStatement.lean`](lean/IndependentExactStatement.lean)
proves `IndependentHomometryAudit.positive_modulus_exact_statement`, expanding
the two project predicates and replacing `[NeZero n]` with `0 < n`. It was
written independently and compiled against the fresh theorem objects. The
fixture does not provide a second independent formal proof of the theorem;
it verifies that the checked theorem implies the intended explicit statement.

## Structural results used

- The one-exchange indicator difference is periodic under the exchanged
  displacement exactly when the two sets are homometric.
- A strict exchange in a `k`-element set has displacement order from `2` to
  `k - 2`; the ambient size is at least `k + order + 1`.
- For cyclic groups, when `k` and the displacement order are even, twice that
  order divides the modulus.
- For six notes these yield the lower bound and divisibility obstruction.
- Symbolic families for `n = 4q`, `q >= 3`, and `n = 3q`, `q >= 5`, prove
  sufficiency. The remaining modulus `12` belongs to the first family.
- The normalized common-set formulation is equivalent to the arbitrary-set
  formulation by proved simultaneous-translation bridges.

The audit checks the theorem and supporting declarations against the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. The bounded computations
are not imported by the Lean proof.

## Claims outside the formal theorem

The paper's count `2 floor(s/2)` for order-four exchanges at `n = 8s` is
mathematically audited and checked over a bounded range, but is not verified
in Lean. It counts unordered pairs of distinct bracelet classes, allowing each
chord its own dihedral equivalence. It does not count simultaneous orbits of
marked configurations or entire homometry classes.

The theorem does not classify all six-note homometric pairs, enumerate all
one-exchange pairs irredundantly, or resolve the unrestricted six-point
classification question. Formal verification does not establish novelty.
