import BassPackedEquiv
/-! Guarded split of the capped bass-bijection draft. -/
namespace Omnibus
set_option maxHeartbeats 20000

def predicateBassEquiv (P : Chord → Prop)
    (hP : ∀ k c, bounded c = true → (P (translate k c) ↔ P c)) :
    {c : PCChord // P (unpackChord c)} ≃
      Fin 12 × {t : PCTriple // P (unpackZero t)} where
  toFun c := (c.val.1, ⟨(normalizePacked c.val).2, by
    rw [unpack_normalized]
    exact (hP _ _ (unpack_bounded c.val)).mpr c.property⟩)
  invFun bt := ⟨denormalizePacked (bt.1,bt.2.val), by
    rw [unpack_denormalized]
    exact (hP _ _ (zero_bounded bt.2.val)).mpr bt.2.property⟩
  left_inv c := by
    apply Subtype.ext
    exact packed_left_inverse c.val
  right_inv bt := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact congrArg Prod.snd (packed_right_inverse (bt.1,bt.2.val))


#print axioms predicateBassEquiv
end Omnibus
