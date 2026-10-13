import Pilot
namespace Omnibus
-- Every edge equation unfolds literal chord and move definitions.
theorem successor_40 : successors ⟨4,7,7⟩ = [] := by decide
theorem successor_41 : successors ⟨4,7,8⟩ = [⟨5,9,9⟩] := by decide
theorem successor_42 : successors ⟨4,7,9⟩ = [] := by decide
theorem successor_43 : successors ⟨4,7,10⟩ = [⟨0,5,8⟩] := by decide
theorem successor_44 : successors ⟨4,7,11⟩ = [⟨0,5,9⟩,⟨1,5,8⟩] := by decide
theorem successor_45 : successors ⟨4,8,8⟩ = [⟨6,9,9⟩] := by decide
theorem successor_46 : successors ⟨4,8,9⟩ = [] := by decide
theorem successor_47 : successors ⟨4,8,11⟩ = [⟨0,6,9⟩,⟨1,5,9⟩] := by decide
#print axioms successor_40
#print axioms successor_41
#print axioms successor_42
#print axioms successor_43
#print axioms successor_44
#print axioms successor_45
#print axioms successor_46
#print axioms successor_47
end Omnibus
