import GoldenAPInterface
import GoldenStepMinimum

/-! Source formalization; see the exact replay receipt for verification status. Exact integer endpoint counting without irrationality. -/
namespace AlgebraicTunings

/-- The manuscript's count, in a floor-only form with strict positive endpoint. -/
noncomputable def goldenLineCount (phi : ℝ) (m : ℤ) (r : ℝ) : ℤ :=
  Int.floor ((-(m : ℝ) + r) / 2) - Int.floor (-(m : ℝ) * phi)

theorem goldenLineCount_eq_floor_add_ceil (phi : ℝ) (m : ℤ) (r : ℝ) :
    goldenLineCount phi m r =
      Int.floor ((-(m : ℝ) + r) / 2) + Int.ceil ((m : ℝ) * phi) := by
  unfold goldenLineCount
  rw [show -(m : ℝ) * phi = -((m : ℝ) * phi) by ring,
    Int.floor_neg]
  ring

/-- A positive first note gives the exact lower integer endpoint. -/
theorem golden_positive_lower_index (phi : ℝ) (m b : ℤ)
    (hpos : 0 < goldenEval phi m b) :
    Int.floor (-(m : ℝ) * phi) < b := by
  apply Int.floor_lt.mpr
  unfold goldenEval at hpos
  linarith

/-- A norm upper bound gives the exact upper integer endpoint. -/
theorem golden_norm_upper_index (m b B : ℤ) (r : ℝ)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = 5 * (m : ℝ) ^ 2 + 4 * B)
    (hN : goldenNorm m b ≤ B) :
    b ≤ Int.floor ((-(m : ℝ) + r) / 2) := by
  have hidZ := goldenNorm_complete_square m b
  have hid : 4 * (goldenNorm m b : ℝ) =
      (2 * (b : ℝ) + m) ^ 2 - 5 * (m : ℝ) ^ 2 := by exact_mod_cast hidZ
  have hNR : (goldenNorm m b : ℝ) ≤ (B : ℝ) := by exact_mod_cast hN
  have hy : 2 * (b : ℝ) + m ≤ r := by
    by_contra hn
    have hl : r < 2 * (b : ℝ) + m := lt_of_not_ge hn
    have hp : 0 < (2 * (b : ℝ) + m - r) * (2 * (b : ℝ) + m + r) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  apply Int.le_floor.mpr
  linarith

/-- Any consecutive positive run has at most the displayed number of terms. -/
theorem golden_unit_run_count_upper (phi : ℝ) (m b B : ℤ) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = 5 * (m : ℝ) ^ 2 + 4 * B)
    (hpos : 0 < goldenEval phi m b)
    (hlast : goldenNorm m (b + (n : ℤ)) ≤ B) :
    (n : ℤ) + 1 ≤ goldenLineCount phi m r := by
  have hlo := golden_positive_lower_index phi m b hpos
  have hhi := golden_norm_upper_index m (b + (n : ℤ)) B r hr hrsq hlast
  unfold goldenLineCount
  omega

/-- The exact endpoint count is within one of the positive frequency root. -/
theorem goldenLineCount_gt_root_sub_one (phi : ℝ) (m : ℤ) (r : ℝ) :
    (-(m : ℝ) + r) / 2 + (m : ℝ) * phi - 1 <
      (goldenLineCount phi m r : ℝ) := by
  have hlo := Int.sub_one_lt_floor ((-(m : ℝ) + r) / 2)
  have hhi := Int.floor_le (-(m : ℝ) * phi)
  unfold goldenLineCount
  push_cast
  linarith

#check @golden_unit_run_count_upper
#print axioms goldenLineCount_eq_floor_add_ceil
#print axioms golden_positive_lower_index
#print axioms golden_norm_upper_index
#print axioms golden_unit_run_count_upper
#print axioms goldenLineCount_gt_root_sub_one
end AlgebraicTunings
