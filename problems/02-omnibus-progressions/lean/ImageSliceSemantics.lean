import ImageEnumerationSemantics
import DisjointSliceCardinality
/-! Instantiates the disjoint slice equivalence with intrinsic images. -/
namespace Omnibus
set_option maxHeartbeats 30000

theorem image_slice_membership (x : Fin 12) (c : Chord) :
    c ∈ imageSlice x.val ↔
      bounded c = true ∧ c.bass = 0 ∧ c.tenor = x.val ∧ inImage c = true := by
  simp only [imageSlice,List.mem_dedup,List.mem_filter,imageRaw_membership,beq_iff_eq]
  constructor
  · rintro ⟨⟨hb,hzero,hi⟩,ht⟩
    exact ⟨hb,hzero,ht,hi⟩
  · rintro ⟨hb,hzero,ht,hi⟩
    exact ⟨⟨hb,hzero,hi⟩,ht⟩

theorem approachable_slice_membership (x : Fin 12) (c : Chord) :
    c ∈ approachableSlice x.val ↔ bounded c = true ∧ c.bass = 0 ∧
      c.tenor = x.val ∧ (chord c = true ∧ inImage c = true) := by
  simp only [approachableSlice,List.mem_filter,image_slice_membership,
    List.contains_iff_mem,sourceRaw_membership]
  constructor
  · rintro ⟨⟨hb,hzero,ht,hi⟩,_,hc⟩
    exact ⟨hb,hzero,ht,hc,hi⟩
  · rintro ⟨hb,hzero,ht,hc,hi⟩
    exact ⟨⟨hb,hzero,ht,hi⟩,hzero,hc⟩

theorem image_slice_nodup (x : Fin 12) : (imageSlice x.val).Nodup := List.nodup_dedup _
theorem approachable_slice_nodup (x : Fin 12) : (approachableSlice x.val).Nodup :=
  List.Nodup.filter _ (image_slice_nodup x)

theorem normalized_image_cardinality_eq_slices :
    Nat.card {t : PCTriple // inImage (unpackZero t) = true} =
      ∑ x : Fin 12, (imageSlice x.val).length := by
  exact disjoint_slice_cardinality (fun c => inImage c = true)
    (fun x => imageSlice x.val) image_slice_membership image_slice_nodup

theorem normalized_approachable_cardinality_eq_slices :
    Nat.card {t : PCTriple // chord (unpackZero t) = true ∧ inImage (unpackZero t) = true} =
      ∑ x : Fin 12, (approachableSlice x.val).length := by
  exact disjoint_slice_cardinality (fun c => chord c = true ∧ inImage c = true)
    (fun x => approachableSlice x.val) approachable_slice_membership approachable_slice_nodup

#print axioms image_slice_membership
#print axioms approachable_slice_membership
#print axioms normalized_image_cardinality_eq_slices
#print axioms normalized_approachable_cardinality_eq_slices
end Omnibus
