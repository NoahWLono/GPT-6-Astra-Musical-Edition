import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_6_9 : (imageCell 6 9).length = 11 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_6_9
theorem approachable_cell_count_6_9 : (approachableCell 6 9).length = 6 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_6_9
theorem image_cell_count_6_10 : (imageCell 6 10).length = 11 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_6_10
theorem approachable_cell_count_6_10 : (approachableCell 6 10).length = 1 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_6_10
theorem image_cell_count_6_11 : (imageCell 6 11).length = 8 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_6_11
theorem approachable_cell_count_6_11 : (approachableCell 6 11).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_6_11
end Omnibus
