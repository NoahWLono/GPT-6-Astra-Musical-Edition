import Pilot
/-! Intrinsic modular and permutation lemmas. -/
namespace Omnibus

def translate (k : Nat) (c : Chord) : Chord :=
  ⟨(c.bass+k)%12,(c.tenor+k)%12,(c.alto+k)%12,(c.soprano+k)%12⟩

-- Intended universal arithmetic bridge, rather than finite case assumptions.
theorem interval_translation (x y k : Nat) (hx : x < 12) (hy : y < 12) :
    interval ((x+k)%12) ((y+k)%12) = interval x y := by
  unfold interval
  omega

theorem modular_translation_injective (x y k : Nat)
    (hx : x < 12) (hy : y < 12) :
    ((x+k)%12 = (y+k)%12) ↔ x = y := by omega

-- Upper-permutation invariance is a symbolic Boolean identity. This avoids
-- testing all 1728 ordered zero-bass states merely to forget upper order.
theorem chord_swap_tenor_alto (b t a s : Nat) :
    chord ⟨b,a,t,s⟩ = chord ⟨b,t,a,s⟩ := by
  simp only [chord, bounded, reorderings, List.any_cons, List.any_nil,
    Bool.or_false]
  ac_rfl

theorem chord_cycle_upper (b t a s : Nat) :
    chord ⟨b,a,s,t⟩ = chord ⟨b,t,a,s⟩ := by
  simp only [chord, bounded, reorderings, List.any_cons, List.any_nil,
    Bool.or_false]
  ac_rfl

#print axioms interval_translation
#print axioms modular_translation_injective
#print axioms chord_swap_tenor_alto
#print axioms chord_cycle_upper
end Omnibus
