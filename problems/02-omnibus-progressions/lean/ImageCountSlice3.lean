import ImageCountDefinitions
/-! Three kernel count certificates for fixed tenor 3. -/
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem source_count_slice_3 : (sourceSlice 3).length = 40 := by decide
theorem image_count_slice_3 : (imageSlice 3).length = 16 := by decide
theorem approachable_count_slice_3 : (approachableSlice 3).length = 12 := by decide
#print axioms source_count_slice_3
#print axioms image_count_slice_3
#print axioms approachable_count_slice_3
end Omnibus
