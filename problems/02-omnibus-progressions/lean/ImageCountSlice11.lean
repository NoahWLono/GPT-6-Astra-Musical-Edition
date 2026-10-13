import ImageCellPartition
import ImageCellBlock11_0
import ImageCellBlock11_1
import ImageCellBlock11_2
import ImageCellBlock11_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets11 (y : Nat) : Nat :=
  match y with
  | 0 => 0
  | 1 => 4
  | 2 => 1
  | 3 => 2
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 6
  | 8 => 3
  | 9 => 2
  | 10 => 4
  | 11 => 0
  | _ => 0

theorem image_cell_row_11 (y : Fin 12) :
    (imageCell 11 y.val).length = imageCellTargets11 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_11_0
  · subst y; exact image_cell_count_11_1
  · subst y; exact image_cell_count_11_2
  · subst y; exact image_cell_count_11_3
  · subst y; exact image_cell_count_11_4
  · subst y; exact image_cell_count_11_5
  · subst y; exact image_cell_count_11_6
  · subst y; exact image_cell_count_11_7
  · subst y; exact image_cell_count_11_8
  · subst y; exact image_cell_count_11_9
  · subst y; exact image_cell_count_11_10
  · subst y; exact image_cell_count_11_11

def approachableCellTargets11 (y : Nat) : Nat :=
  match y with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | _ => 0

theorem approachable_cell_row_11 (y : Fin 12) :
    (approachableCell 11 y.val).length = approachableCellTargets11 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_11_0
  · subst y; exact approachable_cell_count_11_1
  · subst y; exact approachable_cell_count_11_2
  · subst y; exact approachable_cell_count_11_3
  · subst y; exact approachable_cell_count_11_4
  · subst y; exact approachable_cell_count_11_5
  · subst y; exact approachable_cell_count_11_6
  · subst y; exact approachable_cell_count_11_7
  · subst y; exact approachable_cell_count_11_8
  · subst y; exact approachable_cell_count_11_9
  · subst y; exact approachable_cell_count_11_10
  · subst y; exact approachable_cell_count_11_11

theorem image_count_slice_11 : (imageSlice 11).length = 44 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 11 y).length := image_slice_partition 11
    _ = ∑ y ∈ Finset.range 12, imageCellTargets11 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_11 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_11

theorem approachable_count_slice_11 : (approachableSlice 11).length = 6 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 11 y).length := approachable_slice_partition 11
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets11 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_11 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_11

end Omnibus
