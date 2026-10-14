import CanonicalBridge
/-! Split after the capped quotient attempt. -/
namespace Omnibus

deriving instance ReflBEq, LawfulBEq for Shape

def swapUpper (c : Chord) : Chord := ⟨c.bass,c.alto,c.tenor,c.soprano⟩
def cycleUpper (c : Chord) : Chord := ⟨c.bass,c.alto,c.soprano,c.tenor⟩

theorem sort3_swap (x y z : Nat) : sort3 y x z = sort3 x y z := by
  simp only [sort3]
  congr 1 <;> omega

theorem sort3_cycle (x y z : Nat) : sort3 y z x = sort3 x y z := by
  simp only [sort3]
  congr 1 <;> omega

theorem sonority_swap (c : Chord) : sonority (swapUpper c) = sonority c := by
  exact sort3_swap _ _ _
theorem sonority_cycle (c : Chord) : sonority (cycleUpper c) = sonority c := by
  exact sort3_cycle _ _ _
theorem chord_swap (c : Chord) : chord (swapUpper c) = chord c := by
  exact chord_swap_tenor_alto _ _ _ _
theorem chord_cycle (c : Chord) : chord (cycleUpper c) = chord c := by
  exact chord_cycle_upper _ _ _ _


#print axioms sort3_swap
#print axioms sort3_cycle
#print axioms sonority_swap
#print axioms sonority_cycle
#print axioms chord_swap
#print axioms chord_cycle
end Omnibus
