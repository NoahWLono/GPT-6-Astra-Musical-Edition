import ImageCellDefinitions
import ImageRawCertificate
namespace Omnibus
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem image_cell_count_4_3 : (imageCell 4 3).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_4_3
theorem approachable_cell_count_4_3 : (approachableCell 4 3).length = 0 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_4_3
theorem image_cell_count_4_4 : (imageCell 4 4).length = 4 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_4_4
theorem approachable_cell_count_4_4 : (approachableCell 4 4).length = 2 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_4_4
theorem image_cell_count_4_5 : (imageCell 4 5).length = 4 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms image_cell_count_4_5
theorem approachable_cell_count_4_5 : (approachableCell 4 5).length = 2 := by
  simp only [approachableCell,imageCell,imageRaw_eq_literal,sourceRaw_eq_literal]
  decide
#print axioms approachable_cell_count_4_5
end Omnibus
