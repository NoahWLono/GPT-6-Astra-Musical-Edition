import ImageCellPartition
import ImageCellBlock7_0
import ImageCellBlock7_1
import ImageCellBlock7_2
import ImageCellBlock7_3
namespace Omnibus
set_option maxHeartbeats 10000

def imageCellTargets7 (y : Nat) : Nat :=
  match y with
  | 0 => 1
  | 1 => 4
  | 2 => 3
  | 3 => 3
  | 4 => 7
  | 5 => 6
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 7
  | 10 => 9
  | 11 => 6
  | _ => 0

theorem image_cell_row_7 (y : Fin 12) :
    (imageCell 7 y.val).length = imageCellTargets7 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact image_cell_count_7_0
  · subst y; exact image_cell_count_7_1
  · subst y; exact image_cell_count_7_2
  · subst y; exact image_cell_count_7_3
  · subst y; exact image_cell_count_7_4
  · subst y; exact image_cell_count_7_5
  · subst y; exact image_cell_count_7_6
  · subst y; exact image_cell_count_7_7
  · subst y; exact image_cell_count_7_8
  · subst y; exact image_cell_count_7_9
  · subst y; exact image_cell_count_7_10
  · subst y; exact image_cell_count_7_11

def approachableCellTargets7 (y : Nat) : Nat :=
  match y with
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 3
  | 4 => 5
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | _ => 0

theorem approachable_cell_row_7 (y : Fin 12) :
    (approachableCell 7 y.val).length = approachableCellTargets7 y.val := by
  rcases y with ⟨y,hy⟩
  have hh : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst y; exact approachable_cell_count_7_0
  · subst y; exact approachable_cell_count_7_1
  · subst y; exact approachable_cell_count_7_2
  · subst y; exact approachable_cell_count_7_3
  · subst y; exact approachable_cell_count_7_4
  · subst y; exact approachable_cell_count_7_5
  · subst y; exact approachable_cell_count_7_6
  · subst y; exact approachable_cell_count_7_7
  · subst y; exact approachable_cell_count_7_8
  · subst y; exact approachable_cell_count_7_9
  · subst y; exact approachable_cell_count_7_10
  · subst y; exact approachable_cell_count_7_11

theorem image_count_slice_7 : (imageSlice 7).length = 52 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (imageCell 7 y).length := image_slice_partition 7
    _ = ∑ y ∈ Finset.range 12, imageCellTargets7 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact image_cell_row_7 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms image_count_slice_7

theorem approachable_count_slice_7 : (approachableSlice 7).length = 16 := by
  calc
    _ = ∑ y ∈ Finset.range 12, (approachableCell 7 y).length := approachable_slice_partition 7
    _ = ∑ y ∈ Finset.range 12, approachableCellTargets7 y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact approachable_cell_row_7 ⟨y,Finset.mem_range.mp hy⟩
    _ = _ := by decide
#print axioms approachable_count_slice_7

end Omnibus
