import Pilot
namespace Omnibus
-- Every edge equation unfolds literal chord and move definitions.
theorem successor_16 : successors ⟨3,3,6⟩ = [⟨4,4,8⟩] := by decide
theorem successor_17 : successors ⟨3,3,7⟩ = [⟨4,5,8⟩,⟨4,4,9⟩] := by decide
theorem successor_18 : successors ⟨3,3,8⟩ = [⟨4,5,9⟩] := by decide
theorem successor_19 : successors ⟨3,3,9⟩ = [] := by decide
theorem successor_20 : successors ⟨3,4,8⟩ = [⟨5,5,9⟩,⟨4,6,9⟩] := by decide
theorem successor_21 : successors ⟨3,5,8⟩ = [⟨4,7,9⟩] := by decide
theorem successor_22 : successors ⟨3,5,9⟩ = [⟨4,7,10⟩] := by decide
theorem successor_23 : successors ⟨3,6,6⟩ = [⟨4,7,8⟩] := by decide
#print axioms successor_16
#print axioms successor_17
#print axioms successor_18
#print axioms successor_19
#print axioms successor_20
#print axioms successor_21
#print axioms successor_22
#print axioms successor_23
end Omnibus
