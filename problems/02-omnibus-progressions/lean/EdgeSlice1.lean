import Pilot
namespace Omnibus
-- Every edge equation unfolds literal chord and move definitions.
theorem successor_8 : successors ⟨0,5,9⟩ = [] := by decide
theorem successor_9 : successors ⟨0,6,9⟩ = [] := by decide
theorem successor_10 : successors ⟨1,4,8⟩ = [⟨3,5,9⟩,⟨2,6,9⟩] := by decide
theorem successor_11 : successors ⟨1,5,8⟩ = [⟨3,6,9⟩] := by decide
theorem successor_12 : successors ⟨1,5,9⟩ = [⟨3,6,10⟩] := by decide
theorem successor_13 : successors ⟨2,5,8⟩ = [⟨4,6,9⟩,⟨3,7,9⟩,⟨3,6,10⟩] := by decide
theorem successor_14 : successors ⟨2,5,9⟩ = [⟨3,7,10⟩] := by decide
theorem successor_15 : successors ⟨2,6,9⟩ = [⟨4,7,10⟩,⟨3,7,11⟩] := by decide
#print axioms successor_8
#print axioms successor_9
#print axioms successor_10
#print axioms successor_11
#print axioms successor_12
#print axioms successor_13
#print axioms successor_14
#print axioms successor_15
end Omnibus
