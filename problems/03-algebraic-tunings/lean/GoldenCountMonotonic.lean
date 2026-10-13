import GoldenCounting

/-! Source formalization; consult the exact replay receipt for verification status. Direct endpoint monotonicity, with no induction. -/
namespace AlgebraicTunings

/-- Root monotonicity plus integer shifts prove monotonicity of the exact count. -/
theorem goldenLineCount_mono (phi : ℝ) (hphi : 1 ≤ phi)
    (m M B : ℤ) (r R : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hrsq : r ^ 2 = 5 * (m : ℝ) ^ 2 + 4 * B)
    (hRsq : R ^ 2 = 5 * (M : ℝ) ^ 2 + 4 * B) :
    goldenLineCount phi m r ≤ goldenLineCount phi M R := by
  have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hmMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hMR : (0 : ℝ) ≤ M := by linarith
  have hmsq : (m : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := (sq_le_sq₀ hmR hMR).mpr hmMR
  have hroot : r ≤ R := (sq_le_sq₀ hr hR).mp (by nlinarith only [hrsq, hRsq, hmsq])
  have hupper : (-(m : ℝ) + r) / 2 ≤
      (-(M : ℝ) + R) / 2 + ((M - m : ℤ) : ℝ) := by
    push_cast
    linarith
  have hfloor := Int.floor_mono hupper
  rw [Int.floor_add_intCast] at hfloor
  have hprod : 0 ≤ ((M : ℝ) - m) * (phi - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hlower : (m : ℝ) * phi + ((M - m : ℤ) : ℝ) ≤ (M : ℝ) * phi := by
    push_cast
    nlinarith only [hprod]
  have hceil := Int.ceil_mono hlower
  rw [Int.ceil_add_intCast] at hceil
  rw [goldenLineCount_eq_floor_add_ceil, goldenLineCount_eq_floor_add_ceil]
  omega

#check @goldenLineCount_mono
#print axioms goldenLineCount_mono
end AlgebraicTunings
