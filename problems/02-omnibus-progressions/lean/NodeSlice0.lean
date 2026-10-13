import SliceDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
-- Intrinsic classification slice checked by the Lean kernel.
theorem node_slice_0 : nodeSlice 0 = [⟨0,3,6⟩,⟨0,3,7⟩,⟨0,3,8⟩,⟨0,3,9⟩,⟨0,4,7⟩,⟨0,4,8⟩,⟨0,4,9⟩,⟨0,5,8⟩,⟨0,5,9⟩,⟨0,6,9⟩] := by decide
#print axioms node_slice_0
end Omnibus
