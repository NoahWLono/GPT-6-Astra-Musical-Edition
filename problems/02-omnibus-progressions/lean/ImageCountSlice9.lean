import ImageCellPartition
import ImageCellBlock9_0
import ImageCellBlock9_1
import ImageCellBlock9_2
import ImageCellBlock9_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets9 (y : Nat) : Nat :=
  match y with
  | 0 => 3
  | 1 => 4
  | 2 => 4
  | 3 => 3
  | 4 => 11
  | 5 => 12
  | 6 => 11
  | 7 => 7
  | 8 => 3
  | 9 => 4
  | 10 => 3
  | 11 => 2
  | _ => 0

theorem image_cell_row_9 (y : Fin 12) :
    (imageCell 9 y.val).length = imageCellTargets9 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_9_0
  · subst y; exact image_cell_count_9_1
  · subst y; exact image_cell_count_9_2
  · subst y; exact image_cell_count_9_3
  · subst y; exact image_cell_count_9_4
  · subst y; exact image_cell_count_9_5
  · subst y; exact image_cell_count_9_6
  · subst y; exact image_cell_count_9_7
  · subst y; exact image_cell_count_9_8
  · subst y; exact image_cell_count_9_9
  · subst y; exact image_cell_count_9_10
  · subst y; exact image_cell_count_9_11

def approachableCellTargets9 (y : Nat) : Nat :=
  match y with
  | 0 => 3
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 7
  | 5 => 7
  | 6 => 6
  | 7 => 2
  | 8 => 1
  | 9 => 3
  | 10 => 0
  | 11 => 0
  | _ => 0

theorem approachable_cell_row_9 (y : Fin 12) :
    (approachableCell 9 y.val).length = approachableCellTargets9 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_9_0
  · subst y; exact approachable_cell_count_9_1
  · subst y; exact approachable_cell_count_9_2
  · subst y; exact approachable_cell_count_9_3
  · subst y; exact approachable_cell_count_9_4
  · subst y; exact approachable_cell_count_9_5
  · subst y; exact approachable_cell_count_9_6
  · subst y; exact approachable_cell_count_9_7
  · subst y; exact approachable_cell_count_9_8
  · subst y; exact approachable_cell_count_9_9
  · subst y; exact approachable_cell_count_9_10
  · subst y; exact approachable_cell_count_9_11

theorem image_count_slice_9 : (imageSlice 9).length = 67 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 9 y).length := image_slice_partition 9
    _ = ∑ y ∈ Finset.range 12, imageCellTargets9 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_9 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_9

theorem approachable_count_slice_9 : (approachableSlice 9).length = 35 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 9 y).length := approachable_slice_partition 9
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets9 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_9 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_9

end Omnibus
