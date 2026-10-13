import ImageCellPartition
import ImageCellBlock8_0
import ImageCellBlock8_1
import ImageCellBlock8_2
import ImageCellBlock8_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets8 (y : Nat) : Nat :=
  match y with
  | 0 => 3
  | 1 => 4
  | 2 => 2
  | 3 => 1
  | 4 => 9
  | 5 => 9
  | 6 => 7
  | 7 => 2
  | 8 => 2
  | 9 => 3
  | 10 => 7
  | 11 => 3
  | _ => 0

theorem image_cell_row_8 (y : Fin 12) :
    (imageCell 8 y.val).length = imageCellTargets8 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_8_0
  · subst y; exact image_cell_count_8_1
  · subst y; exact image_cell_count_8_2
  · subst y; exact image_cell_count_8_3
  · subst y; exact image_cell_count_8_4
  · subst y; exact image_cell_count_8_5
  · subst y; exact image_cell_count_8_6
  · subst y; exact image_cell_count_8_7
  · subst y; exact image_cell_count_8_8
  · subst y; exact image_cell_count_8_9
  · subst y; exact image_cell_count_8_10
  · subst y; exact image_cell_count_8_11

def approachableCellTargets8 (y : Nat) : Nat :=
  match y with
  | 0 => 2
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 7
  | 5 => 5
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 0
  | 11 => 1
  | _ => 0

theorem approachable_cell_row_8 (y : Fin 12) :
    (approachableCell 8 y.val).length = approachableCellTargets8 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_8_0
  · subst y; exact approachable_cell_count_8_1
  · subst y; exact approachable_cell_count_8_2
  · subst y; exact approachable_cell_count_8_3
  · subst y; exact approachable_cell_count_8_4
  · subst y; exact approachable_cell_count_8_5
  · subst y; exact approachable_cell_count_8_6
  · subst y; exact approachable_cell_count_8_7
  · subst y; exact approachable_cell_count_8_8
  · subst y; exact approachable_cell_count_8_9
  · subst y; exact approachable_cell_count_8_10
  · subst y; exact approachable_cell_count_8_11

theorem image_count_slice_8 : (imageSlice 8).length = 52 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 8 y).length := image_slice_partition 8
    _ = ∑ y ∈ Finset.range 12, imageCellTargets8 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_8 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_8

theorem approachable_count_slice_8 : (approachableSlice 8).length = 21 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 8 y).length := approachable_slice_partition 8
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets8 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_8 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_8

end Omnibus
