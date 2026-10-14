import DifferenceTableDefinition
namespace DifferenceTableResearch

theorem rational_table_complete (p q : ℕ) (π : Fin 10 → Fin 10) (w : QRow)
    (h : TableHolds p q π (fun i => (w i : ℝ))) : RationalTableHolds p q π w := by
  rcases h with ⟨h0, hr, hc⟩
  refine ⟨?_, ?_, ?_⟩
  · change (w 0 : ℝ) = 1 at h0
    exact_mod_cast h0
  · intro e
    have he := hr e
    rw [qEval_cast] at he
    exact_mod_cast he
  · intro c hm
    apply (lex_cast_iff c.1 (c.2.map (fun r => qDot r w))).mp
    rw [List.map_map]
    change LexSatisfied c.1 (c.2.map (fun r => (qDot r w : ℝ)))
    simpa only [qEval_cast] using hc c hm

theorem distinct_samples_sound {n k : ℕ} (params : Fin n → ℕ × ℕ)
    (maps : Fin n → Fin 10 → Fin 10) (samples : Fin n → Fin k → QRow)
    (checked : ∀ i j, i ≠ j → ∃ a,
      RationalTableHolds (params i).1 (params i).2 (maps i) (samples i a) ∧
      ¬RationalTableHolds (params j).1 (params j).2 (maps j) (samples i a)) :
    ∀ i j, i ≠ j → ∃ z,
      TableHolds (params i).1 (params i).2 (maps i) z ∧
      ¬TableHolds (params j).1 (params j).2 (maps j) z := by
  intro i j hij
  obtain ⟨a, hi, hj⟩ := checked i j hij
  refine ⟨fun t => (samples i a t : ℝ), rational_table_sound _ _ _ _ hi, ?_⟩
  intro h
  exact hj (rational_table_complete _ _ _ _ h)
end DifferenceTableResearch
