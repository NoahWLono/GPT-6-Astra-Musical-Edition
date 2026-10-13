import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-!
# Algebraic tunings: elementary formalization core

Status: elementary core compiled under Lean 4.32.2; see the replay receipt.
No `sorry` or additional axioms are used.
The eventual optimal-length theorem is not asserted in this file yet.
This file isolates polynomial identities and the explicit eleven-note witness.
-/

namespace AlgebraicTunings

/-- Norm of `a * φ + b`, where `φ² = φ + 1`. -/
def goldenNorm (a b : ℤ) : ℤ := b * b + a * b - a * a

/-- The norm along a lattice arithmetic progression is quadratic. -/
theorem goldenNorm_along_progression (a b c d k : ℤ) :
    goldenNorm (a + k * c) (b + k * d) =
      goldenNorm a b + k * (2 * b * d + a * d + b * c - 2 * a * c) +
        k * k * goldenNorm c d := by
  unfold goldenNorm
  ring

/-- Pair multiplication in the integral golden ring preserves the norm. -/
theorem goldenNorm_mul (a b c d : ℤ) :
    goldenNorm (a * c + a * d + b * c) (a * c + b * d) =
      goldenNorm a b * goldenNorm c d := by
  unfold goldenNorm
  ring

/-- Conjugation preserves the norm. -/
theorem goldenNorm_conj (a b : ℤ) :
    goldenNorm (-a) (a + b) = goldenNorm a b := by
  unfold goldenNorm
  ring

/-- Multiplication by the conjugate has zero irrational coordinate. -/
theorem mul_conj_first (a b : ℤ) :
    a * (-a) + a * (a + b) + b * (-a) = 0 := by
  ring

/-- Multiplication by the conjugate has norm as rational coordinate. -/
theorem mul_conj_second (a b : ℤ) :
    a * (-a) + b * (a + b) = goldenNorm a b := by
  unfold goldenNorm
  ring

/-- The quadratic interpolation error is exactly `s * (1 - s)`. -/
theorem monic_quadratic_interpolation (p q u s : ℝ) :
    (u + s) ^ 2 + p * (u + s) + q =
      (1 - s) * (u ^ 2 + p * u + q) +
      s * ((u + 1) ^ 2 + p * (u + 1) + q) - s * (1 - s) := by
  ring

/-- The interpolation error never exceeds one quarter. -/
theorem interpolation_error_le_quarter (s : ℝ) :
    s * (1 - s) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (s - 1 / 2)]

/-- The interpolation error is nonnegative inside a unit interval. -/
theorem interpolation_error_nonneg (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 ≤ s * (1 - s) := by
  exact mul_nonneg h0 (sub_nonneg.mpr h1)

/-- Unit-step norms are a completed square (denominators cleared). -/
theorem goldenNorm_complete_square (m b : ℤ) :
    4 * goldenNorm m b = (2 * b + m) ^ 2 - 5 * m ^ 2 := by
  unfold goldenNorm
  ring

/-- Exact norm bounds for the eleven-term witness. -/
theorem eleven_term_norm_bound (j : Fin 11) :
    |goldenNorm 4 ((j.val : ℤ) - 6)| ≤ 20 := by
  fin_cases j <;> norm_num [goldenNorm]

/-- The same witness is positive for the positive golden root. -/
theorem eleven_term_positive (phi : ℝ) (hphi : 3 / 2 < phi) (j : Fin 11) :
    0 < 4 * phi - 6 + (j.val : ℝ) := by
  have hj : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
  linarith

/-- Its adjacent frequencies have exactly the same difference tone. -/
theorem witness_common_difference (phi : ℝ) (j : ℕ) :
    (4 * phi - 6 + ((j + 1 : ℕ) : ℝ)) -
      (4 * phi - 6 + (j : ℝ)) = 1 := by
  push_cast
  ring

/-- The common difference itself belongs to every norm scale with B ≥ 1. -/
theorem common_difference_norm : goldenNorm 0 1 = 1 := by
  norm_num [goldenNorm]

end AlgebraicTunings

#print axioms AlgebraicTunings.goldenNorm_along_progression
#print axioms AlgebraicTunings.goldenNorm_mul
#print axioms AlgebraicTunings.goldenNorm_conj
#print axioms AlgebraicTunings.mul_conj_first
#print axioms AlgebraicTunings.mul_conj_second
#print axioms AlgebraicTunings.monic_quadratic_interpolation
#print axioms AlgebraicTunings.interpolation_error_le_quarter
#print axioms AlgebraicTunings.interpolation_error_nonneg
#print axioms AlgebraicTunings.goldenNorm_complete_square
#print axioms AlgebraicTunings.eleven_term_norm_bound
#print axioms AlgebraicTunings.eleven_term_positive
#print axioms AlgebraicTunings.witness_common_difference
#print axioms AlgebraicTunings.common_difference_norm
