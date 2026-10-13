import GoldenExact

namespace IndependentGoldenAudit
open AlgebraicTunings

/-- Independently stated complete finite extremum, using the manuscript's formula. -/
theorem exact_statement (B : ℕ) (hB : 64 ≤ B) :
    let phi : ℝ := (1 + Real.sqrt 5) / 2
    let M : ℤ := (Nat.sqrt ((4 * B + 3) / 5) : ℤ)
    let F : ℤ := Int.floor ((-(M : ℝ) + Real.sqrt (5 * (M : ℝ) ^ 2 + 4 * B)) / 2) +
      Int.ceil ((M : ℝ) * phi)
    (∃ n : ℕ, ∃ P : GoldenAP phi (B : ℤ) n, (n : ℤ) + 1 = F) ∧
    (∀ n : ℕ, ∀ P : GoldenAP phi (B : ℤ) n, (n : ℤ) + 1 ≤ F) ∧
    (∀ n : ℕ, ∀ P : GoldenAP phi (B : ℤ) n,
      (n : ℤ) + 1 = F → |goldenNorm P.c P.d| = 1) := by
  simpa only [goldenMaximumLength_formula, goldenThresholdIndex, goldenPhi]
    using golden_exact_maximum B hB

#print AlgebraicTunings.GoldenAP
#print AlgebraicTunings.goldenNorm
#print AlgebraicTunings.goldenPhi
#print AlgebraicTunings.goldenThresholdIndex
#print AlgebraicTunings.goldenMaximumLength
#check @AlgebraicTunings.golden_exact_maximum
#check @AlgebraicTunings.goldenMaximumLength_formula
#check @IndependentGoldenAudit.exact_statement
#print axioms AlgebraicTunings.golden_exact_maximum
#print axioms AlgebraicTunings.goldenMaximumLength_formula
#print axioms IndependentGoldenAudit.exact_statement
end IndependentGoldenAudit
