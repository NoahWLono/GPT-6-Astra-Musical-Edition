import GoldenAPInterface

/-! Source formalization; consult the exact replay receipt for verification status. All sufficiently long progressions have unit step. -/
namespace AlgebraicTunings

theorem goldenAP_long_step_unit (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (B : ℤ) (n : ℕ) (P : GoldenAP phi B n) (hB : 64 ≤ B)
    (z s r : ℝ) (hz : 0 ≤ z) (hzsq : z ^ 2 = B)
    (hs : 0 ≤ s) (hssq : s ^ 2 = 2)
    (hr : 0 ≤ r)
    (hrsq : r ^ 2 = (B : ℝ) / |(goldenNorm P.c P.d : ℝ)| + 1 / 4)
    (hlong : (1 + s) * z - 3 < (n : ℝ) + 1) :
    |goldenNorm P.c P.d| = 1 := by
  have hB0 : 0 ≤ B := by omega
  have hBR : (64 : ℝ) ≤ B := by exact_mod_cast hB
  have hqZ := goldenNorm_abs_pos P.c P.d
    (goldenEval_pos_coords_ne phi P.c P.d P.step_pos)
  by_contra hnot
  have hq2Z : 2 ≤ |goldenNorm P.c P.d| := by omega
  have hq2 : (2 : ℝ) ≤ |(goldenNorm P.c P.d : ℝ)| := by exact_mod_cast hq2Z
  have hdiv : (B : ℝ) / |(goldenNorm P.c P.d : ℝ)| ≤ (B : ℝ) / 2 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hq2
  have hz8 : 8 ≤ z := by nlinarith only [hz, hzsq, hBR]
  have hroot : r ≤ (3 : ℝ) / 4 * z := by
    apply (sq_le_sq₀ hr (by nlinarith : 0 ≤ (3 : ℝ) / 4 * z)).mp
    nlinarith only [hrsq, hzsq, hdiv, hBR]
  have hglobal := goldenAP_global_span_bound phi hphi B n P hB0 r s hr hrsq hs hssq
  have hmul := mul_le_mul_of_nonneg_left hroot (by linarith : 0 ≤ 1 + s)
  have hs1 : 1 < s := by nlinarith only [hs, hssq]
  have hpos : 0 < (s - 1) * z := mul_pos (by linarith) (by linarith)
  have hlarge : 16 < (1 + s) * z := by nlinarith only [hpos, hz8]
  nlinarith only [hlong, hglobal, hmul, hlarge]

#check @goldenAP_long_step_unit
#print axioms goldenAP_long_step_unit
end AlgebraicTunings
