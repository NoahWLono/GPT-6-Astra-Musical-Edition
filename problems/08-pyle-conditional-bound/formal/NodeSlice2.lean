import SliceDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
-- Intrinsic classification slice checked by the Lean kernel.
theorem node_slice_2 : nodeSlice 2 = [⟨2,5,8⟩,⟨2,5,9⟩,⟨2,6,9⟩] := by decide
#print axioms node_slice_2
end Omnibus
