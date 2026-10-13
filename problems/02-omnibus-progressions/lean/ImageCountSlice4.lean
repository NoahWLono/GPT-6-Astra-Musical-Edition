import ImageCellPartition
import ImageCellBlock4_0
import ImageCellBlock4_1
import ImageCellBlock4_2
import ImageCellBlock4_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets4 (y : Nat) : Nat :=
  match y with
  | 0 => 3
  | 1 => 4
  | 2 => 4
  | 3 => 0
  | 4 => 4
  | 5 => 4
  | 6 => 3
  | 7 => 7
  | 8 => 9
  | 9 => 11
  | 10 => 9
  | 11 => 7
  | _ => 0

theorem image_cell_row_4 (y : Fin 12) :
    (imageCell 4 y.val).length = imageCellTargets4 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_4_0
  · subst y; exact image_cell_count_4_1
  · subst y; exact image_cell_count_4_2
  · subst y; exact image_cell_count_4_3
  · subst y; exact image_cell_count_4_4
  · subst y; exact image_cell_count_4_5
  · subst y; exact image_cell_count_4_6
  · subst y; exact image_cell_count_4_7
  · subst y; exact image_cell_count_4_8
  · subst y; exact image_cell_count_4_9
  · subst y; exact image_cell_count_4_10
  · subst y; exact image_cell_count_4_11

def approachableCellTargets4 (y : Nat) : Nat :=
  match y with
  | 0 => 3
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 1
  | 7 => 5
  | 8 => 7
  | 9 => 7
  | 10 => 1
  | 11 => 2
  | _ => 0

theorem approachable_cell_row_4 (y : Fin 12) :
    (approachableCell 4 y.val).length = approachableCellTargets4 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_4_0
  · subst y; exact approachable_cell_count_4_1
  · subst y; exact approachable_cell_count_4_2
  · subst y; exact approachable_cell_count_4_3
  · subst y; exact approachable_cell_count_4_4
  · subst y; exact approachable_cell_count_4_5
  · subst y; exact approachable_cell_count_4_6
  · subst y; exact approachable_cell_count_4_7
  · subst y; exact approachable_cell_count_4_8
  · subst y; exact approachable_cell_count_4_9
  · subst y; exact approachable_cell_count_4_10
  · subst y; exact approachable_cell_count_4_11

theorem image_count_slice_4 : (imageSlice 4).length = 65 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 4 y).length := image_slice_partition 4
    _ = ∑ y ∈ Finset.range 12, imageCellTargets4 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_4 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_4

theorem approachable_count_slice_4 : (approachableSlice 4).length = 31 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 4 y).length := approachable_slice_partition 4
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets4 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_4 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_4

end Omnibus
