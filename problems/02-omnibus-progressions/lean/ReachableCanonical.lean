import ReachablePermutations
/-! Guarded, split replacement of the capped ReachableTypes attempt. -/
namespace Omnibus
set_option maxHeartbeats 20000

theorem reachable_sorted (b x y z : Nat) (q : Shape) :
    ReachableType ⟨b,(sort3 x y z).x,(sort3 x y z).y,(sort3 x y z).z⟩ q ↔
      ReachableType ⟨b,x,y,z⟩ q := by
  have h_yxz := reachable_swap ⟨b,x,y,z⟩ q
  have h_yzx := reachable_cycle ⟨b,x,y,z⟩ q
  have h_zxy := (reachable_cycle ⟨b,y,z,x⟩ q).trans h_yzx
  have h_xzy := (reachable_swap ⟨b,x,z,y⟩ q).symm.trans h_zxy
  have h_zyx := (reachable_swap ⟨b,y,z,x⟩ q).trans h_yzx
  rcases sort3_cases x y z with h | h | h | h | h | h
  · rw [h]
  · rw [h]; exact h_xzy
  · rw [h]; exact h_yxz
  · rw [h]; exact h_yzx
  · rw [h]; exact h_zxy
  · rw [h]; exact h_zyx

theorem reachable_canonical (c : Chord) (hc : bounded c = true) (q : Shape) :
    ReachableType (realize (sonority c)) q ↔ ReachableType c q := by
  have hs := reachable_sorted 0 (interval c.bass c.tenor)
    (interval c.bass c.alto) (interval c.bass c.soprano) q
  change ReachableType (realize (sonority c)) q ↔
    ReachableType (normalizeBass c) q at hs
  rw [hs, normalizeBass_eq_translate c hc, reachable_translation]



#print axioms reachable_sorted
#print axioms reachable_canonical
end Omnibus
