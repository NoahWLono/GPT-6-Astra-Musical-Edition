import GoldenExactGeneric
import GoldenThresholdIndex
import GoldenRealBound

/-! Checked formalization; see exact replay receipts. Fully explicit exact extremal theorem for the golden norm scale. -/
namespace AlgebraicTunings

/-- Exact maximum number of notes, with an executable integer threshold. -/
noncomputable def goldenMaximumLength (B : ℕ) : ℤ :=
  goldenLineCount goldenPhi (goldenThresholdIndex B)
    (Real.sqrt (5 * (goldenThresholdIndex B : ℝ) ^ 2 + 4 * B))

/-- For every integer budget B ≥ 64 the explicit count is attained, bounds every
positive nonconstant arithmetic progression, and every maximizer has unit step.
`n` counts gaps, so the number of notes is `n + 1`. -/
theorem golden_exact_maximum (B : ℕ) (hB : 64 ≤ B) :
    (∃ n : ℕ, ∃ P : GoldenAP goldenPhi (B : ℤ) n,
      (n : ℤ) + 1 = goldenMaximumLength B) ∧
    (∀ n : ℕ, ∀ P : GoldenAP goldenPhi (B : ℤ) n,
      (n : ℤ) + 1 ≤ goldenMaximumLength B) ∧
    (∀ n : ℕ, ∀ P : GoldenAP goldenPhi (B : ℤ) n,
      (n : ℤ) + 1 = goldenMaximumLength B → |goldenNorm P.c P.d| = 1) := by
  have h := golden_exact_maximum_generic goldenPhi goldenPhi_equation
    goldenPhi_gt_three_halves Real.sqrt Real.sqrt_nonneg
    (fun _ hx => Real.sq_sqrt hx) (B : ℤ) (goldenThresholdIndex B)
    (by exact_mod_cast hB) (goldenThresholdIndex_nonneg B)
    (goldenThresholdIndex_depth B) (goldenThresholdIndex_next B)
  simpa only [goldenMaximumLength, Int.cast_natCast] using h

/-- The count is the floor-plus-ceiling expression used in the manuscript. -/
theorem goldenMaximumLength_formula (B : ℕ) :
    goldenMaximumLength B =
      Int.floor ((-(goldenThresholdIndex B : ℝ) +
        Real.sqrt (5 * (goldenThresholdIndex B : ℝ) ^ 2 + 4 * B)) / 2) +
      Int.ceil ((goldenThresholdIndex B : ℝ) * goldenPhi) := by
  exact goldenLineCount_eq_floor_add_ceil _ _ _

#check @golden_exact_maximum
#check @goldenMaximumLength_formula
#print axioms golden_exact_maximum
#print axioms goldenMaximumLength_formula
end AlgebraicTunings
