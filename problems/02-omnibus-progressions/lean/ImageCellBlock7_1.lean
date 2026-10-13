import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_7_3 : (imageCell 7 3).length = 3 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_7_3
theorem approachable_cell_count_7_3 : (approachableCell 7 3).length = 3 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_7_3
theorem image_cell_count_7_4 : (imageCell 7 4).length = 7 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_7_4
theorem approachable_cell_count_7_4 : (approachableCell 7 4).length = 5 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_7_4
theorem image_cell_count_7_5 : (imageCell 7 5).length = 6 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_7_5
theorem approachable_cell_count_7_5 : (approachableCell 7 5).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_7_5
end Omnibus
