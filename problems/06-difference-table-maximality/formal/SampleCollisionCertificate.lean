import CollisionDomination

namespace DifferenceTableResearch

theorem samples_bound_collisions {n : ℕ} {I : Type*} (p q : ℕ)
    (π : Fin 10 ≃ Fin 10) (samples : Fin n → QRow) (block : Fin 10 → I)
    (feasible : ∀ k, RationalTableHolds p q π (samples k))
    (separates : ∀ a b, (∀ k, qDot (shortForm p false a) (samples k) =
      qDot (shortForm p false b) (samples k)) → block a = block b) :
    ∀ a b, (∀ z, TableHolds p q π z →
      qEval (shortForm p false a) z = qEval (shortForm p false b) z) → block a = block b := by
  intro a b collision
  apply separates a b
  intro k
  have h := collision (fun j => (samples k j : ℝ))
    (rational_table_sound p q π (samples k) (feasible k))
  simp only [qEval_cast] at h
  exact_mod_cast h

theorem sample_collision_free_maximal {n : ℕ} (p q : ℕ)
    (π : Fin 10 ≃ Fin 10) (samples : Fin n → QRow)
    (feasible : ∀ k, RationalTableHolds p q π (samples k))
    (separates : ∀ a b, (∀ k, qDot (shortForm p false a) (samples k) =
      qDot (shortForm p false b) (samples k)) → a = b) :
    ∀ σ : Fin 10 ≃ Fin 10,
      (∀ z, TableHolds p q π z → TableHolds p q σ z) → σ = π := by
  intro σ inc
  have col := (table_domination_iff p q π σ).mp inc
  have bound := samples_bound_collisions p q π samples id feasible separates
  apply Equiv.ext
  intro e
  simpa using (bound (π e) (σ (π.symm (π e))) (col (π e))).symm

#print axioms sample_collision_free_maximal
end DifferenceTableResearch
