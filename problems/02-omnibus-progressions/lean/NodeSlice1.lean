import SliceDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
-- Intrinsic classification slice checked by the Lean kernel.
theorem node_slice_1 : nodeSlice 1 = [⟨1,4,8⟩,⟨1,5,8⟩,⟨1,5,9⟩] := by decide
#print axioms node_slice_1
end Omnibus
