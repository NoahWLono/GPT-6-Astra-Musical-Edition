import TranslationBridge
/-! Canonical normalization without graph assumptions. -/
namespace Omnibus

theorem sort3_cases (x y z : Nat) :
    sort3 x y z = ⟨x,y,z⟩ ∨ sort3 x y z = ⟨x,z,y⟩ ∨
    sort3 x y z = ⟨y,x,z⟩ ∨ sort3 x y z = ⟨y,z,x⟩ ∨
    sort3 x y z = ⟨z,x,y⟩ ∨ sort3 x y z = ⟨z,y,x⟩ := by
  by_cases hxy : x ≤ y <;> by_cases hyz : y ≤ z <;> by_cases hxz : x ≤ z <;>
    simp [sort3, Shape.mk.injEq, Nat.min_def, Nat.max_def, hxy, hyz, hxz] <;> omega

theorem chord_sorted_upper (b x y z : Nat) :
    chord ⟨b,(sort3 x y z).x,(sort3 x y z).y,(sort3 x y z).z⟩ =
      chord ⟨b,x,y,z⟩ := by
  have h_yxz := chord_swap_tenor_alto b x y z
  have h_yzx := chord_cycle_upper b x y z
  have h_zxy := (chord_cycle_upper b y z x).trans h_yzx
  have h_xzy := (chord_swap_tenor_alto b x z y).symm.trans h_zxy
  have h_zyx := (chord_swap_tenor_alto b y z x).trans h_yzx
  rcases sort3_cases x y z with h | h | h | h | h | h <;>
    rw [h] <;> (first | rfl | exact h_xzy | exact h_yxz | exact h_yzx | exact h_zxy | exact h_zyx)

def normalizeBass (c : Chord) : Chord :=
  ⟨0, interval c.bass c.tenor, interval c.bass c.alto,
    interval c.bass c.soprano⟩

theorem normalizeBass_eq_translate (c : Chord) (hc : bounded c = true) :
    normalizeBass c = translate (12-c.bass) c := by
  obtain ⟨hb, ht, ha, hs⟩ := bounded_fields c hc
  cases c
  dsimp at hb ht ha hs
  simp only [normalizeBass, translate, interval]
  congr 1 <;> omega

theorem canonical_chord (c : Chord) (hc : bounded c = true) :
    chord (realize (sonority c)) = chord c := by
  have hs := chord_sorted_upper 0 (interval c.bass c.tenor)
    (interval c.bass c.alto) (interval c.bass c.soprano)
  change chord (realize (sonority c)) = chord (normalizeBass c) at hs
  rw [hs, normalizeBass_eq_translate c hc, chord_translation _ _ hc]

#print axioms sort3_cases
#print axioms chord_sorted_upper
#print axioms normalizeBass_eq_translate
#print axioms canonical_chord
end Omnibus
