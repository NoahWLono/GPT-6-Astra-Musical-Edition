import ImageCountDefinitions
/-! Three kernel count certificates for fixed tenor 1. -/
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem source_count_slice_1 : (sourceSlice 1).length = 6 := by decide
theorem image_count_slice_1 : (imageSlice 1).length = 34 := by decide
theorem approachable_count_slice_1 : (approachableSlice 1).length = 6 := by decide
#print axioms source_count_slice_1
#print axioms image_count_slice_1
#print axioms approachable_count_slice_1
end Omnibus
