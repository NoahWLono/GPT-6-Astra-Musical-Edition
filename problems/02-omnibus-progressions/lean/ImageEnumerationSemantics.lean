import ImageCountDefinitions
/-! The raw image list must be related to actual image membership
before its finite counts can be used as global chord cardinalities. -/
namespace Omnibus

theorem sorted_upper_in_orderings (x y z : Nat) :
    (⟨0,x,y,z⟩ : Chord) ∈ upperOrderings (sort3 x y z) := by
  rcases sort3_cases x y z with h | h | h | h | h | h <;>
    rw [h] <;> simp [upperOrderings]

theorem upper_orderings_preserve_chord (q : Shape) (c : Chord)
    (h : c ∈ upperOrderings q) : chord c = chord (realize q) := by
  have h_yxz := chord_swap_tenor_alto 0 q.x q.y q.z
  have h_yzx := chord_cycle_upper 0 q.x q.y q.z
  have h_zxy := (chord_cycle_upper 0 q.y q.z q.x).trans h_yzx
  have h_xzy := (chord_swap_tenor_alto 0 q.x q.z q.y).symm.trans h_zxy
  have h_zyx := (chord_swap_tenor_alto 0 q.y q.z q.x).trans h_yzx
  simp only [upperOrderings,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h
  · subst c; rfl
  · subst c; exact h_xzy
  · subst c; exact h_yxz
  · subst c; exact h_yzx
  · subst c; exact h_zxy
  · subst c; exact h_zyx

theorem sourceRaw_membership (c : Chord) :
    c ∈ sourceRaw ↔ c.bass = 0 ∧ chord c = true := by
  constructor
  · intro h
    obtain ⟨q,hq,hc⟩ := List.mem_flatMap.mp h
    have hqn : q ∈ nodes := by simpa only [nodes_exact] using hq
    have hch : chord (realize q) = true := (List.mem_filter.mp hqn).2
    have hb : c.bass = 0 := by
      simp only [upperOrderings,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with h | h | h | h | h | h <;> subst c <;> rfl
    exact ⟨hb,(upper_orderings_preserve_chord q c hc).trans hch⟩
  · rintro ⟨hb,hc⟩
    have hq := chord_type_in_nodes c hc
    rw [nodes_exact] at hq
    apply List.mem_flatMap.mpr
    refine ⟨sonority c,hq,?_⟩
    obtain ⟨hbb,ht,ha,hs⟩ := bounded_fields c (chord_is_bounded c hc)
    cases c with
    | mk b t a s =>
      dsimp at hb ht ha hs
      subst b
      simpa [sonority,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt hs] using sorted_upper_in_orderings t a s

theorem normalizedMove_bass_zero (v : Fin 3) (c : Chord) (hb : c.bass = 0) :
    (normalizedMove v c).bass = 0 := by simp [normalizedMove,translate,step,hb]

theorem normalized_back_recovers (v : Fin 3) (c : Chord)
    (hc : bounded c = true) (hb : c.bass = 0) :
    normalizedMove v (normalizeBass (back v c)) = c := by
  rw [normalizedMove,normalizeBass_eq_translate _ (back_bounded v c),
    step_translation,step_back v c hc]
  obtain ⟨hbb,ht,ha,hs⟩ := bounded_fields c hc
  cases c with
  | mk b t a s =>
    dsimp at hb ht ha hs
    subst b
    simp [translate,back]
    congr 1 <;> omega

theorem imageRaw_membership (c : Chord) :
    c ∈ imageRaw ↔ bounded c = true ∧ c.bass = 0 ∧ inImage c = true := by
  constructor
  · intro h
    obtain ⟨d,hd,hmap⟩ := List.mem_flatMap.mp h
    obtain ⟨v,hv,hc⟩ := List.mem_map.mp hmap
    obtain ⟨hb,hch⟩ := sourceRaw_membership d |>.mp hd
    subst c
    have hbound : bounded (normalizedMove v d) = true := translated_bounded _ _
    refine ⟨hbound,normalizedMove_bass_zero v d hb,?_⟩
    apply (image_membership _ hbound).mpr
    refine ⟨translate 1 d,?_,v,?_⟩
    · rw [chord_translation _ _ (chord_is_bounded d hch)]
      exact hch
    · exact step_translation v 1 d
  · rintro ⟨hbound,hbass,himage⟩
    obtain ⟨v,hv,hback⟩ := List.any_eq_true.mp himage
    apply List.mem_flatMap.mpr
    refine ⟨normalizeBass (back v c),?_,?_⟩
    · apply (sourceRaw_membership _).mpr
      refine ⟨rfl,?_⟩
      rw [normalizeBass_eq_translate _ (back_bounded v c),
        chord_translation _ _ (back_bounded v c)]
      exact hback
    · exact List.mem_map.mpr ⟨v,hv,normalized_back_recovers v c hbound hbass⟩

#print axioms sourceRaw_membership
#print axioms normalized_back_recovers
#print axioms imageRaw_membership
end Omnibus
