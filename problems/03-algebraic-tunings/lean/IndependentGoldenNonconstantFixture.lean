import GoldenExact
namespace IndependentGoldenAudit
open AlgebraicTunings
/-- The attaining witness really has at least two notes, not merely a positive
formal step attached to a singleton. -/
theorem nonconstant_attainment (B : ℕ) (hB : 64 ≤ B) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ P : GoldenAP goldenPhi (B : ℤ) n,
      (n : ℤ) + 1 = goldenMaximumLength B := by
  have hBZ : (4 : ℤ) ≤ (B : ℤ) := by exact_mod_cast (show 4 ≤ B by omega)
  let two : GoldenAP goldenPhi (B : ℤ) 1 := {
    a := 0, b := 1, c := 0, d := 1
    start_pos := by norm_num [goldenEval]
    step_pos := by norm_num [goldenEval]
    norm_bound := by
      intro j hj
      have hjcases : j = 0 ∨ j = 1 := by omega
      rcases hjcases with rfl | rfl <;> norm_num [goldenNorm] <;> omega }
  have h := golden_exact_maximum B hB
  have htwo := h.2.1 1 two
  obtain ⟨n, P, hn⟩ := h.1
  exact ⟨n, by omega, P, hn⟩

#check @nonconstant_attainment
#print axioms nonconstant_attainment
end IndependentGoldenAudit
