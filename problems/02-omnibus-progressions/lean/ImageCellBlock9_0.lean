import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_9_0 : (imageCell 9 0).length = 3 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_9_0
theorem approachable_cell_count_9_0 : (approachableCell 9 0).length = 3 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_9_0
theorem image_cell_count_9_1 : (imageCell 9 1).length = 4 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_9_1
theorem approachable_cell_count_9_1 : (approachableCell 9 1).length = 1 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_9_1
theorem image_cell_count_9_2 : (imageCell 9 2).length = 4 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_9_2
theorem approachable_cell_count_9_2 : (approachableCell 9 2).length = 2 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_9_2
end Omnibus
