import SliceDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
-- Intrinsic classification slice checked by the Lean kernel.
theorem node_slice_3 : nodeSlice 3 = [⟨3,3,6⟩,⟨3,3,7⟩,⟨3,3,8⟩,⟨3,3,9⟩,⟨3,4,8⟩,⟨3,5,8⟩,⟨3,5,9⟩,⟨3,6,6⟩,⟨3,6,8⟩,⟨3,6,9⟩,⟨3,6,10⟩,⟨3,7,7⟩,⟨3,7,8⟩,⟨3,7,9⟩,⟨3,7,10⟩,⟨3,7,11⟩,⟨3,8,8⟩,⟨3,9,9⟩] := by decide
#print axioms node_slice_3
end Omnibus
