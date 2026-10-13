import ImageCellPartition
import ImageCellBlock10_0
import ImageCellBlock10_1
import ImageCellBlock10_2
import ImageCellBlock10_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets10 (y : Nat) : Nat :=
  match y with
  | 0 => 1
  | 1 => 5
  | 2 => 4
  | 3 => 3
  | 4 => 9
  | 5 => 11
  | 6 => 11
  | 7 => 9
  | 8 => 7
  | 9 => 3
  | 10 => 4
  | 11 => 4
  | _ => 0

theorem image_cell_row_10 (y : Fin 12) :
    (imageCell 10 y.val).length = imageCellTargets10 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_10_0
  · subst y; exact image_cell_count_10_1
  · subst y; exact image_cell_count_10_2
  · subst y; exact image_cell_count_10_3
  · subst y; exact image_cell_count_10_4
  · subst y; exact image_cell_count_10_5
  · subst y; exact image_cell_count_10_6
  · subst y; exact image_cell_count_10_7
  · subst y; exact image_cell_count_10_8
  · subst y; exact image_cell_count_10_9
  · subst y; exact image_cell_count_10_10
  · subst y; exact image_cell_count_10_11

def approachableCellTargets10 (y : Nat) : Nat :=
  match y with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | _ => 0

theorem approachable_cell_row_10 (y : Fin 12) :
    (approachableCell 10 y.val).length = approachableCellTargets10 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_10_0
  · subst y; exact approachable_cell_count_10_1
  · subst y; exact approachable_cell_count_10_2
  · subst y; exact approachable_cell_count_10_3
  · subst y; exact approachable_cell_count_10_4
  · subst y; exact approachable_cell_count_10_5
  · subst y; exact approachable_cell_count_10_6
  · subst y; exact approachable_cell_count_10_7
  · subst y; exact approachable_cell_count_10_8
  · subst y; exact approachable_cell_count_10_9
  · subst y; exact approachable_cell_count_10_10
  · subst y; exact approachable_cell_count_10_11

theorem image_count_slice_10 : (imageSlice 10).length = 71 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 10 y).length := image_slice_partition 10
    _ = ∑ y ∈ Finset.range 12, imageCellTargets10 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_10 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_10

theorem approachable_count_slice_10 : (approachableSlice 10).length = 6 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 10 y).length := approachable_slice_partition 10
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets10 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_10 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_10

end Omnibus
