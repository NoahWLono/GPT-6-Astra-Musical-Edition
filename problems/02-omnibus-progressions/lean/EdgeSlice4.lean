import Pilot
namespace Omnibus
-- Every edge equation unfolds literal chord and move definitions.
theorem successor_32 : successors ⟨3,8,8⟩ = [⟨5,9,9⟩] := by decide
theorem successor_33 : successors ⟨3,9,9⟩ = [] := by decide
theorem successor_34 : successors ⟨4,4,7⟩ = [⟨5,5,9⟩] := by decide
theorem successor_35 : successors ⟨4,4,8⟩ = [] := by decide
theorem successor_36 : successors ⟨4,4,9⟩ = [] := by decide
theorem successor_37 : successors ⟨4,5,8⟩ = [⟨6,6,9⟩] := by decide
theorem successor_38 : successors ⟨4,5,9⟩ = [] := by decide
theorem successor_39 : successors ⟨4,6,9⟩ = [] := by decide
#print axioms successor_32
#print axioms successor_33
#print axioms successor_34
#print axioms successor_35
#print axioms successor_36
#print axioms successor_37
#print axioms successor_38
#print axioms successor_39
end Omnibus
