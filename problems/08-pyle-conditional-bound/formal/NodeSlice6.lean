import SliceDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
-- Intrinsic classification slice checked by the Lean kernel.
theorem node_slice_6 : nodeSlice 6 = [⟨6,6,9⟩,⟨6,9,9⟩] := by decide
#print axioms node_slice_6
end Omnibus
