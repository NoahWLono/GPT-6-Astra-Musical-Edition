import BassPackedEquiv
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.List.Dedup
/-! Exact finite equivalence to disjoint tenor-indexed slices.
The tenor index is recovered from each chord; no disjointness is assumed. -/
namespace Omnibus
set_option maxHeartbeats 30000

noncomputable def packZero (c : Chord) (hc : bounded c = true) : PCTriple :=
  let h := bounded_fields c hc
  (⟨c.tenor,h.2.1⟩,⟨c.alto,h.2.2.1⟩,⟨c.soprano,h.2.2.2⟩)

theorem unpack_packZero (c : Chord) (hc : bounded c = true) (hb : c.bass = 0) :
    unpackZero (packZero c hc) = c := by
  cases c with
  | mk b t a s =>
    dsimp at hb
    subst b
    rfl

theorem packZero_unpack (t : PCTriple) : packZero (unpackZero t) (zero_bounded t) = t := by
  rcases t with ⟨t,a,s⟩
  rfl

def SliceMember (L : Fin 12 → List Chord) (x : Fin 12) :=
  {c : Chord // c ∈ (L x).toFinset}

noncomputable def packedTripleSliceEquiv (P : Chord → Prop) (L : Fin 12 → List Chord)
    (hmem : ∀ x c, c ∈ L x ↔
      bounded c = true ∧ c.bass = 0 ∧ c.tenor = x.val ∧ P c) :
    {t : PCTriple // P (unpackZero t)} ≃ Σ x : Fin 12, SliceMember L x where
  toFun t := ⟨t.val.1, ⟨unpackZero t.val, List.mem_toFinset.mpr
    ((hmem t.val.1 (unpackZero t.val)).mpr ⟨zero_bounded t.val,rfl,rfl,t.property⟩)⟩⟩
  invFun xc :=
    let h := (hmem xc.1 xc.2.val).mp (List.mem_toFinset.mp xc.2.property)
    ⟨packZero xc.2.val h.1, by rw [unpack_packZero _ h.1 h.2.1]; exact h.2.2.2⟩
  left_inv t := by
    apply Subtype.ext
    rcases t with ⟨⟨t,a,s⟩,ht⟩
    rfl
  right_inv xc := by
    rcases xc with ⟨⟨x,hx⟩,⟨⟨b,t,a,s⟩,hc⟩⟩
    have h := (hmem ⟨x,hx⟩ ⟨b,t,a,s⟩).mp (List.mem_toFinset.mp hc)
    have hb : b = 0 := h.2.1
    have ht : t = x := h.2.2.1
    subst b
    subst t
    rfl

theorem disjoint_slice_cardinality (P : Chord → Prop) (L : Fin 12 → List Chord)
    (hmem : ∀ x c, c ∈ L x ↔
      bounded c = true ∧ c.bass = 0 ∧ c.tenor = x.val ∧ P c)
    (hnodup : ∀ x, (L x).Nodup) :
    Nat.card {t : PCTriple // P (unpackZero t)} = ∑ x : Fin 12, (L x).length := by
  have hfinite : ∀ x, Finite (SliceMember L x) := by
    intro x
    letI : Fintype (SliceMember L x) := Fintype.ofFinset (L x).toFinset (fun c => Iff.rfl)
    exact Finite.of_fintype _
  letI := hfinite
  calc
    _ = Nat.card (Σ x : Fin 12, SliceMember L x) :=
      Nat.card_congr (packedTripleSliceEquiv P L hmem)
    _ = ∑ x : Fin 12, Nat.card (SliceMember L x) := Nat.card_sigma
    _ = ∑ x : Fin 12, (L x).toFinset.card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Nat.card_eq_finsetCard (L x).toFinset
    _ = ∑ x : Fin 12, (L x).length := by
      apply Finset.sum_congr rfl
      intro x hx
      exact List.toFinset_card_of_nodup (hnodup x)

#print axioms packedTripleSliceEquiv
#print axioms disjoint_slice_cardinality
end Omnibus
