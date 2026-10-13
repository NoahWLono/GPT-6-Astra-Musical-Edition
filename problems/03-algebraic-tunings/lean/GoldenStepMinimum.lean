import GoldenNormCore
import Mathlib.Algebra.Order.Floor.Ring

/-! Source formalization; see the exact replay receipt for verification status. Exact integer minimum for a normalized unit-step line. -/
namespace AlgebraicTunings

/-- Completing the square and integrality prove the lower norm bound. -/
theorem goldenNorm_lower_bound_of_discrete_depth (m b B : ℤ)
    (hdepth : (5 * m * m) / 4 ≤ B) : -B ≤ goldenNorm m b := by
  have hmod : 5 * m * m ≤ 4 * B + 3 := by omega
  have hid := goldenNorm_complete_square m b
  have hs := sq_nonneg (2 * b + m)
  have hfour : -4 * B - 3 ≤ 4 * goldenNorm m b := by nlinarith
  omega

/-- An integer nearest the quadratic vertex realizes the exact minimum. -/
theorem goldenNorm_at_integer_vertex (m : ℤ) :
    goldenNorm m (-(m / 2)) = -((5 * m * m) / 4) := by
  have hcases : m % 2 = 0 ∨ m % 2 = 1 := by omega
  generalize hk : m / 2 = k at *
  rcases hcases with he | ho
  · have hm : m = 2 * k := by omega
    rw [hm]
    unfold goldenNorm
    ring_nf
    omega
  · have hm : m = 2 * k + 1 := by omega
    rw [hm]
    unfold goldenNorm
    ring_nf
    omega

/-- Crossing the threshold creates an explicit forbidden integer sample. -/
theorem goldenNorm_forbidden_vertex (m B : ℤ)
    (hdepth : B < (5 * m * m) / 4) :
    goldenNorm m (-(m / 2)) < -B := by
  rw [goldenNorm_at_integer_vertex]
  omega

#check @goldenNorm_lower_bound_of_discrete_depth
#check @goldenNorm_at_integer_vertex
#print axioms goldenNorm_lower_bound_of_discrete_depth
#print axioms goldenNorm_at_integer_vertex
#print axioms goldenNorm_forbidden_vertex
end AlgebraicTunings
