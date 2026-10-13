import LocalQuotientLift
/-! Shared translation/inverse semantics for the image-count proof. -/
namespace Omnibus

theorem back_bounded (v : Fin 3) (c : Chord) : bounded (back v c) = true := by
  simp [bounded, back, Nat.mod_lt]

theorem back_translation (v : Fin 3) (k : Nat) (c : Chord) :
    back v (translate k c) = translate k (back v c) := by
  cases c
  simp only [back, translate]
  congr 1 <;> omega

theorem step_back (v : Fin 3) (c : Chord) (hc : bounded c = true) :
    step v (back v c) = c := by
  obtain ⟨hb,ht,ha,hs⟩ := bounded_fields c hc
  have hv := v.isLt
  have hcases : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
  rcases v with ⟨v,hv⟩
  cases c
  dsimp at hb ht ha hs hcases
  rcases hcases with h | h | h <;> subst v <;>
    simp [step,back] <;> congr 1 <;> omega

theorem back_step (v : Fin 3) (c : Chord) (hc : bounded c = true) :
    back v (step v c) = c := by
  obtain ⟨hb,ht,ha,hs⟩ := bounded_fields c hc
  have hv := v.isLt
  have hcases : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
  rcases v with ⟨v,hv⟩
  cases c
  dsimp at hb ht ha hs hcases
  rcases hcases with h | h | h <;> subst v <;>
    simp [step,back] <;> congr 1 <;> omega

theorem image_translation (k : Nat) (c : Chord) :
    inImage (translate k c) = inImage c := by
  unfold inImage
  apply List.any_congr rfl
  intro v
  rw [back_translation, chord_translation _ _ (back_bounded v c)]

theorem image_membership (c : Chord) (hc : bounded c = true) :
    inImage c = true ↔ ∃ d : Chord, chord d = true ∧
      ∃ v : Fin 3, step v d = c := by
  simp only [inImage, List.any_eq_true]
  constructor
  · rintro ⟨v,hv,hd⟩
    exact ⟨back v c,hd,v,step_back v c hc⟩
  · rintro ⟨d,hd,v,hv⟩
    refine ⟨v,?_,?_⟩
    · have hh := v.isLt
      have hcases : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
      simp only [voices, List.mem_cons, List.not_mem_nil, or_false]
      rcases hcases with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    · rw [← hv, back_step v d (chord_is_bounded d hd)]
      exact hd

#print axioms step_back
#print axioms back_step
#print axioms image_translation
#print axioms image_membership
end Omnibus
