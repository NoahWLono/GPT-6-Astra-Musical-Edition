import ImageCellDefinitions
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_4_0 : (imageCell 4 0).length = 3 := by decide
#print axioms image_cell_count_4_0
theorem approachable_cell_count_4_0 : (approachableCell 4 0).length = 3 := by decide
#print axioms approachable_cell_count_4_0
theorem image_cell_count_4_1 : (imageCell 4 1).length = 4 := by decide
#print axioms image_cell_count_4_1
theorem approachable_cell_count_4_1 : (approachableCell 4 1).length = 1 := by decide
#print axioms approachable_cell_count_4_1
theorem image_cell_count_4_2 : (imageCell 4 2).length = 4 := by decide
#print axioms image_cell_count_4_2
theorem approachable_cell_count_4_2 : (approachableCell 4 2).length = 0 := by decide
#print axioms approachable_cell_count_4_2
end Omnibus
