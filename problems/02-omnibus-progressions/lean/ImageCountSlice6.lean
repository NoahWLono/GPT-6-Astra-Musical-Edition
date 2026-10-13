import ImageCellPartition
import ImageCellBlock6_0
import ImageCellBlock6_1
import ImageCellBlock6_2
import ImageCellBlock6_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets6 (y : Nat) : Nat :=
  match y with
  | 0 => 2
  | 1 => 4
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | 6 => 3
  | 7 => 2
  | 8 => 7
  | 9 => 11
  | 10 => 11
  | 11 => 8
  | _ => 0

theorem image_cell_row_6 (y : Fin 12) :
    (imageCell 6 y.val).length = imageCellTargets6 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_6_0
  · subst y; exact image_cell_count_6_1
  · subst y; exact image_cell_count_6_2
  · subst y; exact image_cell_count_6_3
  · subst y; exact image_cell_count_6_4
  · subst y; exact image_cell_count_6_5
  · subst y; exact image_cell_count_6_6
  · subst y; exact image_cell_count_6_7
  · subst y; exact image_cell_count_6_8
  · subst y; exact image_cell_count_6_9
  · subst y; exact image_cell_count_6_10
  · subst y; exact image_cell_count_6_11

def approachableCellTargets6 (y : Nat) : Nat :=
  match y with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 6
  | 10 => 1
  | 11 => 0
  | _ => 0

theorem approachable_cell_row_6 (y : Fin 12) :
    (approachableCell 6 y.val).length = approachableCellTargets6 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_6_0
  · subst y; exact approachable_cell_count_6_1
  · subst y; exact approachable_cell_count_6_2
  · subst y; exact approachable_cell_count_6_3
  · subst y; exact approachable_cell_count_6_4
  · subst y; exact approachable_cell_count_6_5
  · subst y; exact approachable_cell_count_6_6
  · subst y; exact approachable_cell_count_6_7
  · subst y; exact approachable_cell_count_6_8
  · subst y; exact approachable_cell_count_6_9
  · subst y; exact approachable_cell_count_6_10
  · subst y; exact approachable_cell_count_6_11

theorem image_count_slice_6 : (imageSlice 6).length = 61 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 6 y).length := image_slice_partition 6
    _ = ∑ y ∈ Finset.range 12, imageCellTargets6 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_6 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_6

theorem approachable_count_slice_6 : (approachableSlice 6).length = 13 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 6 y).length := approachable_slice_partition 6
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets6 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_6 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_6

end Omnibus
