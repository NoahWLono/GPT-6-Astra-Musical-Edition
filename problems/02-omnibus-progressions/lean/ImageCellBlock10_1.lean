import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_10_3 : (imageCell 10 3).length = 3 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_10_3
theorem approachable_cell_count_10_3 : (approachableCell 10 3).length = 2 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_10_3
theorem image_cell_count_10_4 : (imageCell 10 4).length = 9 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_10_4
theorem approachable_cell_count_10_4 : (approachableCell 10 4).length = 1 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_10_4
theorem image_cell_count_10_5 : (imageCell 10 5).length = 11 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_10_5
theorem approachable_cell_count_10_5 : (approachableCell 10 5).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_10_5
end Omnibus
