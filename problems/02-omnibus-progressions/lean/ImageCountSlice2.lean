import ImageCountDefinitions
/-! Three kernel count certificates for fixed tenor 2. -/
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem source_count_slice_2 : (sourceSlice 2).length = 6 := by decide
theorem image_count_slice_2 : (imageSlice 2).length = 24 := by decide
theorem approachable_count_slice_2 : (approachableSlice 2).length = 6 := by decide
#print axioms source_count_slice_2
#print axioms image_count_slice_2
#print axioms approachable_count_slice_2
end Omnibus
