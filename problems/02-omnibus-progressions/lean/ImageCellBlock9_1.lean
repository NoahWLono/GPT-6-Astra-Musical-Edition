import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_9_3 : (imageCell 9 3).length = 3 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_9_3
theorem approachable_cell_count_9_3 : (approachableCell 9 3).length = 3 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_9_3
theorem image_cell_count_9_4 : (imageCell 9 4).length = 11 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_9_4
theorem approachable_cell_count_9_4 : (approachableCell 9 4).length = 7 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_9_4
theorem image_cell_count_9_5 : (imageCell 9 5).length = 12 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_9_5
theorem approachable_cell_count_9_5 : (approachableCell 9 5).length = 7 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_9_5
end Omnibus
