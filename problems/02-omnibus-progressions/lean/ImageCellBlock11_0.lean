import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_11_0 : (imageCell 11 0).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_11_0
theorem approachable_cell_count_11_0 : (approachableCell 11 0).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_11_0
theorem image_cell_count_11_1 : (imageCell 11 1).length = 4 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_11_1
theorem approachable_cell_count_11_1 : (approachableCell 11 1).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_11_1
theorem image_cell_count_11_2 : (imageCell 11 2).length = 1 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_11_2
theorem approachable_cell_count_11_2 : (approachableCell 11 2).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_11_2
end Omnibus
