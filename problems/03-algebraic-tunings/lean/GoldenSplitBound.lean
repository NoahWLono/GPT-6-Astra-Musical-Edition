import GoldenStepMinimum

/-! Checked formalization; see exact replay receipts. Sharp squared-span exclusion for a split norm line. -/
namespace AlgebraicTunings

private theorem integer_run_avoids (b k : ℤ) (n : ℕ)
    (havoid : ∀ j : ℕ, j ≤ n → b + (j : ℤ) ≠ k) :
    k < b ∨ b + (n : ℤ) < k := by
  by_cases hkb : k < b
  · exact Or.inl hkb
  · apply Or.inr
    by_contra hbk
    have hnonneg : 0 ≤ k - b := by omega
    let j : ℕ := (k - b).toNat
    have hj : (j : ℤ) = k - b := Int.toNat_of_nonneg hnonneg
    have hjn : j ≤ n := by omega
    have hne := havoid j hjn
    omega

/-- Beyond the discrete vertex threshold, every allowed run has n²≤2B.
This uses only actual integer sample bounds, not a continuous hypothesis. -/
theorem golden_split_run_span_sq (m b B : ℤ) (n : ℕ)
    (hdepth : B < (5 * m * m) / 4)
    (hnorm : ∀ j : ℕ, j ≤ n → |goldenNorm m (b + (j : ℤ))| ≤ B) :
    (n : ℤ) ^ 2 ≤ 2 * B := by
  have hforbid := goldenNorm_forbidden_vertex m B hdepth
  have havoid : ∀ j : ℕ, j ≤ n → b + (j : ℤ) ≠ -(m / 2) := by
    intro j hj heq
    have hlow := (abs_le.mp (hnorm j hj)).1
    rw [heq] at hlow
    omega
  have hside := integer_run_avoids b (-(m / 2)) n havoid
  have hfirst := hnorm 0 (Nat.zero_le n)
  simp only [Nat.cast_zero, add_zero] at hfirst
  rcases abs_le.mp hfirst with ⟨hfL, hfU⟩
  rcases abs_le.mp (hnorm n le_rfl) with ⟨hlL, hlU⟩
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  rcases hside with hright | hleft
  · have hvertex : 0 ≤ 2 * b + m := by omega
    have hp : 0 ≤ (n : ℤ) * (2 * b + m) := mul_nonneg hn0 hvertex
    unfold goldenNorm at hfL hfU hlL hlU
    nlinarith only [hfL, hlU, hp]
  · have hvertex : 0 ≤ -m - 2 * (b + (n : ℤ)) := by omega
    have hp : 0 ≤ (n : ℤ) * (-m - 2 * (b + (n : ℤ))) := mul_nonneg hn0 hvertex
    unfold goldenNorm at hfL hfU hlL hlU
    nlinarith only [hfU, hlL, hp]

#check @golden_split_run_span_sq
#print axioms golden_split_run_span_sq
end AlgebraicTunings
