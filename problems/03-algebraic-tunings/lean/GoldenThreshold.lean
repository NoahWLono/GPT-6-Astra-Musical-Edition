import GoldenStepMinimum
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Checked formalization; see exact replay receipts. Threshold and floor-index facts for the exact formula. -/
namespace AlgebraicTunings

theorem golden_depth_mono (m M : ℤ) (hm : 0 ≤ m) (h : m ≤ M) :
    (5 * m * m) / 4 ≤ (5 * M * M) / 4 := by
  have hM : 0 ≤ M := by omega
  have hsq : m * m ≤ M * M := mul_self_le_mul_self hm h
  exact Int.ediv_le_ediv (by norm_num) (by nlinarith)

/-- A single next-integer inequality certifies that M is the largest allowed line. -/
theorem golden_threshold_max (B M m : ℤ) (hM : 0 ≤ M)
    (hnext : B < (5 * (M + 1) * (M + 1)) / 4)
    (hm : 0 ≤ m) (hdepth : (5 * m * m) / 4 ≤ B) : m ≤ M := by
  by_contra hn
  have hMm : M + 1 ≤ m := by omega
  have hmono := golden_depth_mono (M + 1) m (by omega) hMm
  omega

theorem golden_beyond_threshold (B M m : ℤ) (hM : 0 ≤ M)
    (hnext : B < (5 * (M + 1) * (M + 1)) / 4)
    (hm : M < m) : B < (5 * m * m) / 4 := by
  have hmono := golden_depth_mono (M + 1) m (by omega) (by omega)
  omega

/-- Flooring v with 5v²≤4B automatically gives an unbroken norm line. -/
theorem golden_floor_depth (B : ℤ) (v : ℝ) (hv : 0 ≤ v)
    (hvsq : 5 * v ^ 2 ≤ 4 * B) :
    (5 * Int.floor v * Int.floor v) / 4 ≤ B := by
  have hm : (0 : ℝ) ≤ Int.floor v := by
    exact_mod_cast (Int.floor_nonneg.mpr hv)
  have hmv := Int.floor_le v
  have hmsq : (Int.floor v : ℝ) ^ 2 ≤ v ^ 2 := (sq_le_sq₀ hm hv).mpr hmv
  have hboundR : 5 * (Int.floor v : ℝ) * Int.floor v ≤ 4 * B := by nlinarith
  have hbound : 5 * Int.floor v * Int.floor v ≤ 4 * B := by exact_mod_cast hboundR
  omega

#check @golden_threshold_max
#print axioms golden_depth_mono
#print axioms golden_threshold_max
#print axioms golden_beyond_threshold
#print axioms golden_floor_depth
end AlgebraicTunings
