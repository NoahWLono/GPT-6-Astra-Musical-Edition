import SliceDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
-- Intrinsic classification slice checked by the Lean kernel.
theorem node_slice_4 : nodeSlice 4 = [⟨4,4,7⟩,⟨4,4,8⟩,⟨4,4,9⟩,⟨4,5,8⟩,⟨4,5,9⟩,⟨4,6,9⟩,⟨4,7,7⟩,⟨4,7,8⟩,⟨4,7,9⟩,⟨4,7,10⟩,⟨4,7,11⟩,⟨4,8,8⟩,⟨4,8,9⟩,⟨4,8,11⟩,⟨4,9,9⟩] := by decide
#print axioms node_slice_4
end Omnibus
