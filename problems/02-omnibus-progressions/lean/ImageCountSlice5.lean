import ImageCellPartition
import ImageCellBlock5_0
import ImageCellBlock5_1
import ImageCellBlock5_2
import ImageCellBlock5_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets5 (y : Nat) : Nat :=
  match y with
  | 0 => 3
  | 1 => 5
  | 2 => 3
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 4
  | 7 => 6
  | 8 => 9
  | 9 => 12
  | 10 => 11
  | 11 => 7
  | _ => 0

theorem image_cell_row_5 (y : Fin 12) :
    (imageCell 5 y.val).length = imageCellTargets5 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_5_0
  · subst y; exact image_cell_count_5_1
  · subst y; exact image_cell_count_5_2
  · subst y; exact image_cell_count_5_3
  · subst y; exact image_cell_count_5_4
  · subst y; exact image_cell_count_5_5
  · subst y; exact image_cell_count_5_6
  · subst y; exact image_cell_count_5_7
  · subst y; exact image_cell_count_5_8
  · subst y; exact image_cell_count_5_9
  · subst y; exact image_cell_count_5_10
  · subst y; exact image_cell_count_5_11

def approachableCellTargets5 (y : Nat) : Nat :=
  match y with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | 7 => 0
  | 8 => 5
  | 9 => 7
  | 10 => 0
  | 11 => 0
  | _ => 0

theorem approachable_cell_row_5 (y : Fin 12) :
    (approachableCell 5 y.val).length = approachableCellTargets5 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_5_0
  · subst y; exact approachable_cell_count_5_1
  · subst y; exact approachable_cell_count_5_2
  · subst y; exact approachable_cell_count_5_3
  · subst y; exact approachable_cell_count_5_4
  · subst y; exact approachable_cell_count_5_5
  · subst y; exact approachable_cell_count_5_6
  · subst y; exact approachable_cell_count_5_7
  · subst y; exact approachable_cell_count_5_8
  · subst y; exact approachable_cell_count_5_9
  · subst y; exact approachable_cell_count_5_10
  · subst y; exact approachable_cell_count_5_11

theorem image_count_slice_5 : (imageSlice 5).length = 68 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 5 y).length := image_slice_partition 5
    _ = ∑ y ∈ Finset.range 12, imageCellTargets5 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_5 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_5

theorem approachable_count_slice_5 : (approachableSlice 5).length = 22 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 5 y).length := approachable_slice_partition 5
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets5 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_5 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_5

end Omnibus
