import GoldenAPInterface
import Mathlib.Analysis.Real.Sqrt

/-! Source formalization; see the exact replay receipt for verification status. Explicit real-frequency version of the global bound. -/
namespace AlgebraicTunings

noncomputable def goldenPhi : ℝ := (1 + Real.sqrt 5) / 2

theorem goldenPhi_equation : goldenPhi ^ 2 = goldenPhi + 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  unfold goldenPhi
  nlinarith

theorem goldenPhi_gt_three_halves : (3 : ℝ) / 2 < goldenPhi := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h0 := Real.sqrt_nonneg (5 : ℝ)
  unfold goldenPhi
  nlinarith

/-- Explicit square-root upper bound for any actual golden norm-scale AP. -/
theorem goldenAP_explicit_global_bound (B : ℤ) (n : ℕ)
    (P : GoldenAP goldenPhi B n) (hB : 0 ≤ B) :
    (n : ℝ) ≤ (1 + Real.sqrt 2) *
      Real.sqrt ((B : ℝ) / |(goldenNorm P.c P.d : ℝ)| + 1 / 4) := by
  apply goldenAP_global_span_bound goldenPhi goldenPhi_equation B n P hB
    _ _ (Real.sqrt_nonneg _) _ (Real.sqrt_nonneg _) _
  · apply Real.sq_sqrt
    have hBR : (0 : ℝ) ≤ B := by exact_mod_cast hB
    have hdiv := div_nonneg hBR (abs_nonneg (goldenNorm P.c P.d : ℝ))
    linarith
  · exact Real.sq_sqrt (by norm_num)

#check @goldenAP_explicit_global_bound
#print axioms goldenPhi_equation
#print axioms goldenPhi_gt_three_halves
#print axioms goldenAP_explicit_global_bound
end AlgebraicTunings
