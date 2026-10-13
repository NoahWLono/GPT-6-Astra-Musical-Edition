import GoldenNormCore
import Mathlib.Data.Nat.GCD.Basic

/-!
Source formalization; consult the exact replay receipt for verification status. Elementary norm nonvanishing without importing the
currently uncached golden-ratio/irrationality modules. The coprime-reduction
argument is adapted from Mathlib.NumberTheory.Zsqrtd.Basic, theorems
`divides_sq_eq_zero` and `divides_sq_eq_zero_z` (Apache 2.0, Mario Carneiro).
-/
namespace AlgebraicTunings

private theorem five_not_nat_square (n : ℕ) : 5 ≠ n * n := by
  intro h
  have hn : n ≤ 2 := by
    by_contra hn
    have hn3 : 3 ≤ n := by omega
    have hsq := Nat.mul_le_mul hn3 hn3
    omega
  have hc : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> norm_num at h

private theorem square_eq_five_square_nat {x y : ℕ}
    (h : x * x = 5 * y * y) : x = 0 ∧ y = 0 := by
  let g := x.gcd y
  rcases g.eq_zero_or_pos with hg | hg
  · exact ⟨Nat.eq_zero_of_gcd_eq_zero_left hg,
      Nat.eq_zero_of_gcd_eq_zero_right hg⟩
  · obtain ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := Nat.exists_coprime x y
    rw [hx, hy] at h
    have he : m * m = 5 * (n * n) := by
      refine mul_left_cancel₀ (mul_pos hg hg).ne' ?_
      simpa [g, mul_comm, mul_left_comm, mul_assoc] using h
    have co1 := co.mul_right co
    have co2 := co1.mul_left co1
    have hsquare : 5 = m * m :=
      Nat.dvd_antisymm (by rw [he]; exact dvd_mul_right _ _) <|
        co2.dvd_of_dvd_mul_right (by simp [he])
    exact False.elim (five_not_nat_square m hsquare)

private theorem square_eq_five_square_int {x y : ℤ}
    (h : x * x = 5 * y * y) : x = 0 ∧ y = 0 := by
  have hn : x.natAbs * x.natAbs = 5 * y.natAbs * y.natAbs := by
    have ha := congrArg Int.natAbs h
    simpa [Int.natAbs_mul] using ha
  obtain ⟨hx, hy⟩ := square_eq_five_square_nat hn
  exact ⟨Int.natAbs_eq_zero.mp hx, Int.natAbs_eq_zero.mp hy⟩

/-- A golden integer has zero norm exactly when both coordinates vanish. -/
theorem goldenNorm_eq_zero_iff (a b : ℤ) :
    goldenNorm a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hsq : (2 * b + a) * (2 * b + a) = 5 * a * a := by
      have hc := goldenNorm_complete_square a b
      nlinarith
    obtain ⟨hab, ha⟩ := square_eq_five_square_int hsq
    exact ⟨ha, by omega⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [goldenNorm]

/-- In particular every nonzero common difference has positive absolute norm. -/
theorem goldenNorm_abs_pos (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    0 < |goldenNorm a b| := by
  apply abs_pos.mpr
  intro hn
  obtain ⟨ha, hb⟩ := (goldenNorm_eq_zero_iff a b).mp hn
  rcases h with h | h
  · exact h ha
  · exact h hb

#check @goldenNorm_eq_zero_iff
#check @goldenNorm_abs_pos
#print axioms goldenNorm_eq_zero_iff
#print axioms goldenNorm_abs_pos
end AlgebraicTunings
