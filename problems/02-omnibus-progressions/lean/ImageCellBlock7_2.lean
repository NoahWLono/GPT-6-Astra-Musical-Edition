import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_7_6 : (imageCell 7 6).length = 2 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_7_6
theorem approachable_cell_count_7_6 : (approachableCell 7 6).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_7_6
theorem image_cell_count_7_7 : (imageCell 7 7).length = 2 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_7_7
theorem approachable_cell_count_7_7 : (approachableCell 7 7).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_7_7
theorem image_cell_count_7_8 : (imageCell 7 8).length = 2 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_7_8
theorem approachable_cell_count_7_8 : (approachableCell 7 8).length = 1 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_7_8
end Omnibus
