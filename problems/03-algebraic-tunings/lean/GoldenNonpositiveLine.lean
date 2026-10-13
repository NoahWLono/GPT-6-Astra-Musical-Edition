import GoldenAPInterface

/-! Checked formalization; see exact replay receipts. Negative-coefficient normalized lines are short. -/
namespace AlgebraicTunings

theorem golden_nonpositive_line_span (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (hphi0 : (3 : ℝ) / 2 < phi) (m b B : ℤ) (n : ℕ) (z : ℝ)
    (hm : m ≤ 0) (hz : 0 ≤ z) (hzsq : z ^ 2 = B)
    (hstart : 0 < goldenEval phi m b)
    (hlast : goldenNorm m (b + (n : ℤ)) ≤ B) : (n : ℝ) ≤ z := by
  let x := goldenEval phi m (b + (n : ℤ))
  let y := goldenEval (1 - phi) m (b + (n : ℤ))
  have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx : x = goldenEval phi m b + (n : ℝ) := by
    dsimp [x, goldenEval]
    push_cast
    ring
  have hx0 : 0 ≤ x := by linarith
  have hprod : (m : ℝ) * (2 * phi - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hmR (by linarith)
  have hxy : x ≤ y := by
    dsimp [x, y, goldenEval]
    push_cast
    nlinarith only [hprod]
  have hsq : x ^ 2 ≤ x * y := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hxy hx0
  have hfactor : x * y = (goldenNorm m (b + (n : ℤ)) : ℝ) :=
    goldenNorm_real_factorization phi hphi m (b + (n : ℤ))
  have hlastR : (goldenNorm m (b + (n : ℤ)) : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hlast
  have hxz : x ≤ z := (sq_le_sq₀ hx0 hz).mp (by nlinarith only [hsq, hfactor, hzsq, hlastR])
  linarith

#check @golden_nonpositive_line_span
#print axioms golden_nonpositive_line_span
end AlgebraicTunings
