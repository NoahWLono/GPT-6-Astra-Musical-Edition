import SemanticDraft
/-! Intrinsic translation bridge.
No finite graph or cardinality is assumed. -/
namespace Omnibus

theorem bounded_fields (c : Chord) (h : bounded c = true) :
    c.bass < 12 ∧ c.tenor < 12 ∧ c.alto < 12 ∧ c.soprano < 12 := by
  simpa [bounded, and_assoc] using h

theorem translated_bounded (k : Nat) (c : Chord) :
    bounded (translate k c) = true := by
  simp [bounded, translate, Nat.mod_lt]

theorem translated_distinct (k : Nat) (c : Chord) (hc : bounded c = true) :
    allDistinct (translate k c) = allDistinct c := by
  obtain ⟨hb, ht, ha, hs⟩ := bounded_fields c hc
  apply Bool.eq_iff_iff.mpr
  simp [allDistinct, translate, modular_translation_injective, hb, ht, ha, hs]

theorem translated_stacking (k : Nat) (c : Chord) (hc : bounded c = true) :
    stacking (translate k c) = stacking c := by
  obtain ⟨hb, ht, ha, hs⟩ := bounded_fields c hc
  have hd := translated_distinct k c hc
  simp only [stacking, hd]
  simp [translate, interval_translation, hb, ht, ha, hs]

theorem translate_reorderings (k : Nat) (c : Chord) :
    reorderings (translate k c) = (reorderings c).map (translate k) := by
  cases c
  rfl

theorem reordering_bounded (c d : Chord) (hc : bounded c = true)
    (hd : d ∈ reorderings c) : bounded d = true := by
  obtain ⟨hb, ht, ha, hs⟩ := bounded_fields c hc
  simp only [reorderings, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst d <;> simp [bounded, hb, ht, ha, hs]

theorem chord_translation (k : Nat) (c : Chord) (hc : bounded c = true) :
    chord (translate k c) = chord c := by
  simp only [chord, translated_bounded, hc, Bool.true_and,
    translate_reorderings, List.any_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨e, he, hp⟩
    exact ⟨e, he, (translated_stacking k e (reordering_bounded c e hc he)) ▸ hp⟩
  · rintro ⟨e, he, hp⟩
    exact ⟨e, he, (translated_stacking k e (reordering_bounded c e hc he)).symm ▸ hp⟩

theorem step_translation (v : Fin 3) (k : Nat) (c : Chord) :
    step v (translate k c) = translate k (step v c) := by
  cases c
  simp only [step, translate]
  congr 1 <;> omega

theorem step_bounded (v : Fin 3) (c : Chord) : bounded (step v c) = true := by
  simp [bounded, step, Nat.mod_lt]

theorem sonority_translation (k : Nat) (c : Chord) (hc : bounded c = true) :
    sonority (translate k c) = sonority c := by
  obtain ⟨hb, ht, ha, hs⟩ := bounded_fields c hc
  change sort3 (interval _ _) (interval _ _) (interval _ _) =
    sort3 (interval _ _) (interval _ _) (interval _ _)
  simp only [translate]
  rw [interval_translation _ _ _ hb ht,
    interval_translation _ _ _ hb ha, interval_translation _ _ _ hb hs]

#print axioms chord_translation
#print axioms step_translation
#print axioms sonority_translation
end Omnibus
