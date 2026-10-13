import Pilot
namespace Omnibus
-- Every edge equation unfolds literal chord and move definitions.
theorem successor_0 : successors ⟨0,3,6⟩ = [⟨1,4,8⟩] := by decide
theorem successor_1 : successors ⟨0,3,7⟩ = [⟨1,5,8⟩] := by decide
theorem successor_2 : successors ⟨0,3,8⟩ = [⟨1,5,9⟩] := by decide
theorem successor_3 : successors ⟨0,3,9⟩ = [] := by decide
theorem successor_4 : successors ⟨0,4,7⟩ = [⟨2,5,8⟩,⟨1,5,9⟩] := by decide
theorem successor_5 : successors ⟨0,4,8⟩ = [⟨2,5,9⟩] := by decide
theorem successor_6 : successors ⟨0,4,9⟩ = [] := by decide
theorem successor_7 : successors ⟨0,5,8⟩ = [⟨2,6,9⟩] := by decide
#print axioms successor_0
#print axioms successor_1
#print axioms successor_2
#print axioms successor_3
#print axioms successor_4
#print axioms successor_5
#print axioms successor_6
#print axioms successor_7
end Omnibus
