import ImageCountDefinitions
/-! Three kernel count certificates for fixed tenor 0. -/
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem source_count_slice_0 : (sourceSlice 0).length = 20 := by decide
theorem image_count_slice_0 : (imageSlice 0).length = 16 := by decide
theorem approachable_count_slice_0 : (approachableSlice 0).length = 12 := by decide
#print axioms source_count_slice_0
#print axioms image_count_slice_0
#print axioms approachable_count_slice_0
end Omnibus
