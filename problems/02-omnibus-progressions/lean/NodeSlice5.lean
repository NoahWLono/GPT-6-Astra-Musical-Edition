import SliceDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
-- Intrinsic classification slice checked by the Lean kernel.
theorem node_slice_5 : nodeSlice 5 = [⟨5,5,8⟩,⟨5,5,9⟩,⟨5,8,8⟩,⟨5,9,9⟩] := by decide
#print axioms node_slice_5
end Omnibus
