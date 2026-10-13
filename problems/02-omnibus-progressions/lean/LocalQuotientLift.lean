import ReachableCanonical
/-! Split after the capped quotient attempt. -/
namespace Omnibus

theorem successor_membership (p q : Shape) :
    q ∈ successors p ↔ ReachableType (realize p) q := by
  simp [successors, voices, ReachableType, Fin.exists_fin_succ,
    List.mem_eraseDups, or_and_right, and_or_left, exists_or, and_assoc]

theorem chord_is_bounded (c : Chord) (hc : chord c = true) : bounded c = true := by
  exact (Bool.and_eq_true_iff.mp hc).1

theorem local_quotient_lift (c : Chord) (hc : chord c = true) (q : Shape) :
    q ∈ successors (sonority c) ↔ ∃ d, OmnibusStep c d ∧ sonority d = q := by
  rw [successor_membership, reachable_canonical c (chord_is_bounded c hc)]
  constructor
  · rintro ⟨v, hv, hq⟩
    exact ⟨step v c, ⟨hc,hv,⟨v,rfl⟩⟩, hq⟩
  · rintro ⟨d, ⟨_,hd,v,hv⟩, hq⟩
    exact ⟨v,hv.symm ▸ hd,hv.symm ▸ hq⟩


#print axioms successor_membership
#print axioms chord_is_bounded
#print axioms local_quotient_lift
end Omnibus
