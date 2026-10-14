import ReachableTranslation
/-! Guarded, split replacement of the capped ReachableTypes attempt. -/
namespace Omnibus
set_option maxHeartbeats 20000

theorem reachable_cases (c : Chord) (q : Shape) :
    ReachableType c q ↔
      (chord (step 0 c) = true ∧ sonority (step 0 c) = q) ∨
      (chord (step 1 c) = true ∧ sonority (step 1 c) = q) ∨
      (chord (step 2 c) = true ∧ sonority (step 2 c) = q) := by
  constructor
  · rintro ⟨v,hv⟩
    have hcases : v = 0 ∨ v = 1 ∨ v = 2 := by
      have hvlt := v.isLt
      have hh : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
      rcases hh with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hcases with h | h | h <;> subst v
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩

theorem reachable_swap (c : Chord) (q : Shape) :
    ReachableType (swapUpper c) q ↔ ReachableType c q := by
  rw [reachable_cases, reachable_cases]
  have h0 : step 0 (swapUpper c) = swapUpper (step 1 c) := rfl
  have h1 : step 1 (swapUpper c) = swapUpper (step 0 c) := rfl
  have h2 : step 2 (swapUpper c) = swapUpper (step 2 c) := rfl
  rw [h0,h1,h2,chord_swap,chord_swap,chord_swap,
    sonority_swap,sonority_swap,sonority_swap]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem reachable_cycle (c : Chord) (q : Shape) :
    ReachableType (cycleUpper c) q ↔ ReachableType c q := by
  rw [reachable_cases, reachable_cases]
  have h0 : step 0 (cycleUpper c) = cycleUpper (step 1 c) := rfl
  have h1 : step 1 (cycleUpper c) = cycleUpper (step 2 c) := rfl
  have h2 : step 2 (cycleUpper c) = cycleUpper (step 0 c) := rfl
  rw [h0,h1,h2,chord_cycle,chord_cycle,chord_cycle,
    sonority_cycle,sonority_cycle,sonority_cycle]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · rintro (h | h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)


#print axioms reachable_cases
#print axioms reachable_swap
#print axioms reachable_cycle
end Omnibus
