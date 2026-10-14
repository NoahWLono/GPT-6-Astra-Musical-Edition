import QuotientSymmetry
/-! Guarded, split replacement of the capped ReachableTypes attempt. -/
namespace Omnibus
set_option maxHeartbeats 20000

def ReachableType (c : Chord) (q : Shape) : Prop :=
  ∃ v : Fin 3, chord (step v c) = true ∧ sonority (step v c) = q

theorem reachable_translation (k : Nat) (c : Chord) (q : Shape) :
    ReachableType (translate k c) q ↔ ReachableType c q := by
  unfold ReachableType
  apply exists_congr
  intro v
  rw [step_translation, chord_translation _ _ (step_bounded v c),
    sonority_translation _ _ (step_bounded v c)]


#print axioms reachable_translation
end Omnibus
