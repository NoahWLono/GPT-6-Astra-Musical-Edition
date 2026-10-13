import GoldenCounting

/-! Source formalization; consult the exact replay receipt for verification status. Attainment of every unbroken unit-step line count. -/
namespace AlgebraicTunings

/-- Inside the upper root, a positive golden frequency on a shallow line has
both norm bounds. The proof uses only the actual golden quadratic equation. -/
theorem golden_point_norm_bound (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (hphi0 : (3 : ℝ) / 2 < phi) (m b B : ℤ) (r : ℝ)
    (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = 5 * (m : ℝ) ^ 2 + 4 * B)
    (hdepth : (5 * m * m) / 4 ≤ B)
    (hpos : 0 < goldenEval phi m b)
    (hupper : (b : ℝ) ≤ (-(m : ℝ) + r) / 2) :
    |goldenNorm m b| ≤ B := by
  apply abs_le.mpr
  constructor
  · exact goldenNorm_lower_bound_of_discrete_depth m b B hdepth
  · have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
    have hBR : (0 : ℝ) ≤ B := by exact_mod_cast hB
    have ht0 : 0 ≤ 2 * phi - 1 := by linarith
    have ht2 : (2 * phi - 1) ^ 2 = 5 := by nlinarith
    have hmt0 : 0 ≤ (m : ℝ) * (2 * phi - 1) := mul_nonneg hmR ht0
    have hmt2 : ((m : ℝ) * (2 * phi - 1)) ^ 2 = 5 * (m : ℝ) ^ 2 := by
      rw [mul_pow, ht2]
      ring
    have hmt : (m : ℝ) * (2 * phi - 1) ≤ r := by
      apply (sq_le_sq₀ hmt0 hr).mp
      nlinarith
    have hyL : -r ≤ 2 * (b : ℝ) + m := by
      unfold goldenEval at hpos
      nlinarith
    have hyU : 2 * (b : ℝ) + m ≤ r := by linarith
    have hp : 0 ≤ (r - (2 * (b : ℝ) + m)) * (r + (2 * (b : ℝ) + m)) :=
      mul_nonneg (by linarith) (by linarith)
    have hidZ := goldenNorm_complete_square m b
    have hid : 4 * (goldenNorm m b : ℝ) =
        (2 * (b : ℝ) + m) ^ 2 - 5 * (m : ℝ) ^ 2 := by exact_mod_cast hidZ
    have hNR : (goldenNorm m b : ℝ) ≤ (B : ℝ) := by nlinarith
    exact_mod_cast hNR

/-- The first strict positive lattice point on the m-line. -/
noncomputable def goldenFirstIndex (phi : ℝ) (m : ℤ) : ℤ :=
  Int.floor (-(m : ℝ) * phi) + 1

theorem goldenFirstIndex_positive (phi : ℝ) (m : ℤ) :
    0 < goldenEval phi m (goldenFirstIndex phi m) := by
  have h := Int.lt_floor_add_one (-(m : ℝ) * phi)
  unfold goldenEval goldenFirstIndex
  push_cast
  linarith

/-- A canonical unit-step progression attaining any permitted endpoint count. -/
noncomputable def goldenCanonicalRun (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (hphi0 : (3 : ℝ) / 2 < phi) (m B : ℤ) (n : ℕ) (r : ℝ)
    (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = 5 * (m : ℝ) ^ 2 + 4 * B)
    (hdepth : (5 * m * m) / 4 ≤ B)
    (hcount : (n : ℤ) + 1 ≤ goldenLineCount phi m r) : GoldenAP phi B n where
  a := m
  b := goldenFirstIndex phi m
  c := 0
  d := 1
  start_pos := goldenFirstIndex_positive phi m
  step_pos := by norm_num [goldenEval]
  norm_bound := by
    intro j hj
    simp only [mul_zero, add_zero, mul_one]
    have hjZ : (j : ℤ) ≤ n := by exact_mod_cast hj
    have hindex : goldenFirstIndex phi m + (j : ℤ) ≤
        Int.floor ((-(m : ℝ) + r) / 2) := by
      unfold goldenFirstIndex goldenLineCount at *
      omega
    apply golden_point_norm_bound phi hphi hphi0 m (goldenFirstIndex phi m + (j : ℤ)) B r
      hm hB hr hrsq hdepth
    · have hstart := goldenFirstIndex_positive phi m
      have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      unfold goldenEval at *
      push_cast
      linarith
    · exact Int.le_floor.mp hindex

#check @goldenCanonicalRun
#print axioms golden_point_norm_bound
#print axioms goldenFirstIndex_positive
#print axioms goldenCanonicalRun
end AlgebraicTunings
