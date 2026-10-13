import ImageSliceSemantics
import ActualChordCardinality
import ImageCountSlice0
import ImageCountSlice1
import ImageCountSlice2
import ImageCountSlice3
import ImageCountSlice4
import ImageCountSlice5
import ImageCountSlice6
import ImageCountSlice7
import ImageCountSlice8
import ImageCountSlice9
import ImageCountSlice10
import ImageCountSlice11
namespace Omnibus
set_option maxHeartbeats 15000

def imageTenorTargets (x : Nat) : Nat :=
  match x with
  | 0 => 16
  | 1 => 34
  | 2 => 24
  | 3 => 16
  | 4 => 65
  | 5 => 68
  | 6 => 61
  | 7 => 52
  | 8 => 52
  | 9 => 67
  | 10 => 71
  | 11 => 44
  | _ => 0

theorem image_tenor_counts (x : Fin 12) : (imageSlice x.val).length = imageTenorTargets x.val := by
  rcases x with ⟨x,hx⟩
  have hh : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst x; exact image_count_slice_0
  · subst x; exact image_count_slice_1
  · subst x; exact image_count_slice_2
  · subst x; exact image_count_slice_3
  · subst x; exact image_count_slice_4
  · subst x; exact image_count_slice_5
  · subst x; exact image_count_slice_6
  · subst x; exact image_count_slice_7
  · subst x; exact image_count_slice_8
  · subst x; exact image_count_slice_9
  · subst x; exact image_count_slice_10
  · subst x; exact image_count_slice_11

theorem normalized_image_count_exact :
    Nat.card {t : PCTriple // inImage (unpackZero t) = true} = 570 := by
  calc
    _ = ∑ x : Fin 12, (imageSlice x.val).length := normalized_image_cardinality_eq_slices
    _ = ∑ x : Fin 12, imageTenorTargets x.val := by
      apply Finset.sum_congr rfl
      intro x hx
      exact image_tenor_counts x
    _ = _ := by decide

def approachableTenorTargets (x : Nat) : Nat :=
  match x with
  | 0 => 12
  | 1 => 6
  | 2 => 6
  | 3 => 12
  | 4 => 31
  | 5 => 22
  | 6 => 13
  | 7 => 16
  | 8 => 21
  | 9 => 35
  | 10 => 6
  | 11 => 6
  | _ => 0

theorem approachable_tenor_counts (x : Fin 12) : (approachableSlice x.val).length = approachableTenorTargets x.val := by
  rcases x with ⟨x,hx⟩
  have hh : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 := by omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h
  · subst x; exact approachable_count_slice_0
  · subst x; exact approachable_count_slice_1
  · subst x; exact approachable_count_slice_2
  · subst x; exact approachable_count_slice_3
  · subst x; exact approachable_count_slice_4
  · subst x; exact approachable_count_slice_5
  · subst x; exact approachable_count_slice_6
  · subst x; exact approachable_count_slice_7
  · subst x; exact approachable_count_slice_8
  · subst x; exact approachable_count_slice_9
  · subst x; exact approachable_count_slice_10
  · subst x; exact approachable_count_slice_11

theorem normalized_approachable_count_exact :
    Nat.card {t : PCTriple // chord (unpackZero t) = true ∧ inImage (unpackZero t) = true} = 186 := by
  calc
    _ = ∑ x : Fin 12, (approachableSlice x.val).length := normalized_approachable_cardinality_eq_slices
    _ = ∑ x : Fin 12, approachableTenorTargets x.val := by
      apply Finset.sum_congr rfl
      intro x hx
      exact approachable_tenor_counts x
    _ = _ := by decide

theorem global_image_count_exact :
    Nat.card {c : Chord // ActualImage c} = 6840 := by
  rw [actual_image_cardinality_eq_packed,semantic_image_factor_twelve,
    normalized_image_count_exact]

theorem global_approachable_count_exact :
    Nat.card {c : Chord // chord c = true ∧ ActualImage c} = 2232 := by
  rw [actual_approachable_cardinality_eq_packed,semantic_approachable_factor_twelve,
    normalized_approachable_count_exact]

#print axioms normalized_image_count_exact
#print axioms normalized_approachable_count_exact
#print axioms global_image_count_exact
#print axioms global_approachable_count_exact
end Omnibus
