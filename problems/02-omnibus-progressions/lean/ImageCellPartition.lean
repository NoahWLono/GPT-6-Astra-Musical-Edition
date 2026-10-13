import ImageCellDefinitions
import ImageSliceSemantics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-! Exact disjoint alto partition of each already-defined tenor slice. -/
namespace Omnibus
set_option maxHeartbeats 30000

theorem image_slice_bounded (x : Nat) (c : Chord) (h : c ∈ imageSlice x) :
    bounded c = true := by
  have hr : c ∈ imageRaw := (List.mem_filter.mp (List.mem_dedup.mp h)).1
  exact ((imageRaw_membership c).mp hr).1

theorem image_cell_finset (x y : Nat) :
    (imageCell x y).toFinset = (imageSlice x).toFinset.filter (fun c => c.alto = y) := by
  apply Finset.ext
  intro c
  simp [imageCell,imageSlice,and_assoc]

theorem approachable_cell_finset (x y : Nat) :
    (approachableCell x y).toFinset =
      (approachableSlice x).toFinset.filter (fun c => c.alto = y) := by
  apply Finset.ext
  intro c
  simp [approachableCell,approachableSlice,imageCell,imageSlice,and_assoc,and_left_comm,and_comm]

theorem image_cell_nodup (x y : Nat) : (imageCell x y).Nodup := List.nodup_dedup _
theorem approachable_cell_nodup (x y : Nat) : (approachableCell x y).Nodup :=
  List.Nodup.filter _ (image_cell_nodup x y)

theorem image_slice_partition (x : Nat) :
    (imageSlice x).length = ∑ y ∈ Finset.range 12, (imageCell x y).length := by
  have hm : ((imageSlice x).toFinset : Set Chord).MapsTo Chord.alto (Finset.range 12) := by
    intro c hc
    exact Finset.mem_range.mpr (bounded_fields c
      (image_slice_bounded x c (List.mem_toFinset.mp hc))).2.2.1
  have h := Finset.card_eq_sum_card_fiberwise hm
  have hp := List.toFinset_card_of_nodup (List.nodup_dedup
    (imageRaw.filter fun c => c.tenor == x))
  change (imageSlice x).toFinset.card = (imageSlice x).length at hp
  rw [hp] at h
  calc
    (imageSlice x).length = ∑ y ∈ Finset.range 12,
        ((imageSlice x).toFinset.filter fun c => c.alto = y).card := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← image_cell_finset, List.toFinset_card_of_nodup (image_cell_nodup x y)]

theorem approachable_slice_partition (x : Nat) :
    (approachableSlice x).length = ∑ y ∈ Finset.range 12, (approachableCell x y).length := by
  have hm : ((approachableSlice x).toFinset : Set Chord).MapsTo Chord.alto (Finset.range 12) := by
    intro c hc
    have hi : c ∈ imageSlice x := (List.mem_filter.mp (List.mem_toFinset.mp hc)).1
    exact Finset.mem_range.mpr (bounded_fields c (image_slice_bounded x c hi)).2.2.1
  have h := Finset.card_eq_sum_card_fiberwise hm
  have hn : (approachableSlice x).Nodup := List.Nodup.filter _ (List.nodup_dedup _)
  rw [List.toFinset_card_of_nodup hn] at h
  calc
    (approachableSlice x).length = ∑ y ∈ Finset.range 12,
        ((approachableSlice x).toFinset.filter fun c => c.alto = y).card := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← approachable_cell_finset, List.toFinset_card_of_nodup (approachable_cell_nodup x y)]

#print axioms image_cell_finset
#print axioms approachable_cell_finset
#print axioms image_slice_partition
#print axioms approachable_slice_partition
end Omnibus
