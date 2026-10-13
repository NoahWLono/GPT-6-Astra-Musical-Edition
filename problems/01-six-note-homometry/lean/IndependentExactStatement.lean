import FullSixNoteExistence

open scoped BigOperators

namespace IndependentHomometryAudit

/-- Independently stated in elementary finite-set language, using only n > 0.
No project-specific predicate appears in the statement. -/
theorem positive_modulus_exact_statement (n : ℕ) (hn : 0 < n) :
    (∃ A B : Finset (ZMod n),
      A.card = 6 ∧ B.card = 6 ∧ (A ∩ B).card = 5 ∧
      (∀ t : ZMod n,
        (∑ x ∈ A, (if x - t ∈ A then (1 : ℤ) else 0)) =
        (∑ x ∈ B, (if x - t ∈ B then (1 : ℤ) else 0))) ∧
      ¬ ((∃ t : ZMod n, B = A.image (fun x => x + t)) ∨
         (∃ t : ZMod n, B = A.image (fun x => t - x)))) ↔
      12 ≤ n ∧ (3 ∣ n ∨ 4 ∣ n) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  simpa only [OnePitchShift.Homometric, OnePitchShift.autocorrelation,
    OnePitchShift.indicator, OnePitchShift.DihedralEquivalent] using
    OnePitchShift.six_note_one_exchange_existence_iff n

end IndependentHomometryAudit

#print axioms IndependentHomometryAudit.positive_modulus_exact_statement
#check @IndependentHomometryAudit.positive_modulus_exact_statement
