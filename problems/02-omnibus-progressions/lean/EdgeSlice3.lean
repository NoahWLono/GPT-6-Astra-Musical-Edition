import Pilot
namespace Omnibus
-- Every edge equation unfolds literal chord and move definitions.
theorem successor_24 : successors ⟨3,6,8⟩ = [⟨4,8,9⟩,⟨4,7,10⟩] := by decide
theorem successor_25 : successors ⟨3,6,9⟩ = [⟨4,7,11⟩] := by decide
theorem successor_26 : successors ⟨3,6,10⟩ = [⟨4,8,11⟩,⟨0,4,7⟩] := by decide
theorem successor_27 : successors ⟨3,7,7⟩ = [⟨5,8,8⟩,⟨4,8,9⟩] := by decide
theorem successor_28 : successors ⟨3,7,8⟩ = [⟨4,9,9⟩] := by decide
theorem successor_29 : successors ⟨3,7,9⟩ = [⟨4,8,11⟩] := by decide
theorem successor_30 : successors ⟨3,7,10⟩ = [⟨0,4,8⟩] := by decide
theorem successor_31 : successors ⟨3,7,11⟩ = [⟨0,5,8⟩,⟨0,4,9⟩,⟨1,4,8⟩] := by decide
#print axioms successor_24
#print axioms successor_25
#print axioms successor_26
#print axioms successor_27
#print axioms successor_28
#print axioms successor_29
#print axioms successor_30
#print axioms successor_31
end Omnibus
