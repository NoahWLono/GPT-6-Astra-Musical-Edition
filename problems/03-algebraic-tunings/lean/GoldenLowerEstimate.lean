import GoldenCounting

/-! Source formalization; consult the exact replay receipt for verification status. Derivative-free quantitative lower construction. -/
namespace AlgebraicTunings

/-- A rational Lipschitz bound for the square roots occurring in the construction. -/
theorem golden_root_gap_bound (u v r R : ℝ)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : 0 < v)
    (hr : 3 * u ≤ r) (hR : 3 * v ≤ R)
    (hsq : R ^ 2 - r ^ 2 = 5 * (v ^ 2 - u ^ 2)) :
    R - r ≤ (5 : ℝ) / 3 * (v - u) := by
  have hsum : 0 < R + r := by linarith
  have hprod : 0 ≤ (v - u) * (R + r - 3 * (v + u)) :=
    mul_nonneg (by linarith) (by linarith)
  have hscaled : (3 * (R - r)) * (R + r) ≤
      (5 * (v - u)) * (R + r) := by nlinarith only [hsq, hprod]
  have hfinal := (mul_le_mul_iff_left₀ hsum).mp hscaled
  linarith

/-- Precise lower estimate for the explicit floor-index construction.
All roots are specified by equations, allowing a light algebraic proof module. -/
theorem golden_floor_construction_count_lower
    (phi : ℝ) (hphi : phi ^ 2 = phi + 1) (hphi0 : (3 : ℝ) / 2 < phi)
    (B : ℤ) (z s v r : ℝ)
    (hz : 0 < z) (hzsq : z ^ 2 = B)
    (hs : 0 ≤ s) (hssq : s ^ 2 = 2)
    (hv : (2 * phi - 1) * v = 2 * z)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = 5 * (Int.floor v : ℝ) ^ 2 + 4 * B) :
    (1 + s) * z - 3 < (goldenLineCount phi (Int.floor v) r : ℝ) := by
  let g : ℝ := 2 * phi - 1
  let m : ℤ := Int.floor v
  have hg : 0 < g := by dsimp [g]; linarith
  have hgsq : g ^ 2 = 5 := by dsimp [g]; nlinarith only [hphi]
  have hgBound : g < (7 : ℝ) / 3 := by
    by_contra hn
    have hge : (7 : ℝ) / 3 ≤ g := le_of_not_gt hn
    have hp := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7 / 3) hge
    nlinarith only [hp, hgsq]
  have hgv : g * v = 2 * z := hv
  have hvpos : 0 < v := by
    by_contra hn
    have hvnonpos : v ≤ 0 := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hg) hvnonpos
    linarith
  have hmnonneg : 0 ≤ m := Int.floor_nonneg.mpr (le_of_lt hvpos)
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast hmnonneg
  have hmv : (m : ℝ) ≤ v := Int.floor_le v
  have hvm : v < (m : ℝ) + 1 := Int.lt_floor_add_one v
  have hgv_sq : (g * v) ^ 2 = (2 * z) ^ 2 := congrArg (fun x : ℝ => x ^ 2) hgv
  have hv_sq : 5 * v ^ 2 = 4 * B := by
    rw [mul_pow, hgsq] at hgv_sq
    nlinarith only [hgv_sq, hzsq]
  have hR_sq : (2 * s * z) ^ 2 = 8 * B := by
    calc
      (2 * s * z) ^ 2 = 4 * (s ^ 2) * (z ^ 2) := by ring
      _ = 8 * (B : ℝ) := by rw [hssq, hzsq]; ring
  have hR0 : 0 ≤ 2 * s * z :=
    mul_nonneg (mul_nonneg (by norm_num) hs) (le_of_lt hz)
  have hRlow : 3 * v ≤ 2 * s * z := by
    apply (sq_le_sq₀ (by linarith) hR0).mp
    nlinarith only [hv_sq, hR_sq, sq_nonneg v]
  have hrlow : 3 * (m : ℝ) ≤ r := by
    apply (sq_le_sq₀ (by linarith) hr).mp
    have hvmsq : (m : ℝ) ^ 2 ≤ v ^ 2 := (sq_le_sq₀ hm0 (le_of_lt hvpos)).mpr hmv
    nlinarith only [hrsq, hv_sq, hvmsq, sq_nonneg (m : ℝ)]
  have hdiff : (2 * s * z) ^ 2 - r ^ 2 = 5 * (v ^ 2 - (m : ℝ) ^ 2) := by
    dsimp [m]
    nlinarith only [hR_sq, hrsq, hv_sq]
  have hgap := golden_root_gap_bound (m : ℝ) v r (2 * s * z)
    hm0 hmv hvpos hrlow hRlow hdiff
  have hdelta : g * (v - (m : ℝ)) ≤ g := by
    have hp := mul_le_mul_of_nonneg_left (le_of_lt hvm) (le_of_lt hg)
    nlinarith only [hp]
  have hgapBound : 2 * s * z - r < (5 : ℝ) / 3 := by
    linarith only [hgap, hvm]
  have hendpoint : (1 + s) * z - 2 <
      (-(m : ℝ) + r) / 2 + (m : ℝ) * phi := by
    dsimp [g] at hdelta hgv hgBound
    nlinarith only [hgapBound, hdelta, hgv, hgBound]
  have hcount := goldenLineCount_gt_root_sub_one phi m r
  exact lt_trans (by linarith [hendpoint]) hcount

#check @golden_floor_construction_count_lower
#print axioms golden_root_gap_bound
#print axioms golden_floor_construction_count_lower
end AlgebraicTunings
