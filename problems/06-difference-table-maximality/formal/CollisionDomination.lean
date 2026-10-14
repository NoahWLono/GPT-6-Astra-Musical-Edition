import DifferenceTableDefinition

namespace DifferenceTableResearch
/- The same chamber must be used for every matching. No convexity,
   nonemptiness or rank assumption is needed for this exact criterion. -/
def MatchingLocus {E X V : Type*} (C : X → Prop)
    (source target : E → X → V) (π : E ≃ E) (x : X) : Prop :=
  C x ∧ ∀ e, target e x = source (π e) x

def ForcedCollision {E X V : Type*} (S : X → Prop)
    (source : E → X → V) (a b : E) : Prop :=
  ∀ x, S x → source a x = source b x

theorem matching_domination_iff {E X V : Type*} (C : X → Prop)
    (source target : E → X → V) (π σ : E ≃ E) :
    (∀ x, MatchingLocus C source target π x → MatchingLocus C source target σ x) ↔
    ∀ a, ForcedCollision (MatchingLocus C source target π) source
      a (σ (π.symm a)) := by
  constructor
  · intro inc a x hx
    have hy := inc x hx
    have hπ := hx.2 (π.symm a)
    have hσ := hy.2 (π.symm a)
    simpa using hπ.symm.trans hσ
  · intro collision x hx
    refine ⟨hx.1, ?_⟩
    intro e
    have h := collision (π e) x hx
    simpa using (hx.2 e).trans h

theorem collision_free_dominator_unique {E X V : Type*} (C : X → Prop)
    (source target : E → X → V) (π σ : E ≃ E)
    (free : ∀ a b, ForcedCollision (MatchingLocus C source target π) source a b → a = b)
    (inc : ∀ x, MatchingLocus C source target π x → MatchingLocus C source target σ x) :
    σ = π := by
  have h := (matching_domination_iff C source target π σ).mp inc
  ext e
  simpa using (free (π e) (σ (π.symm (π e))) (h (π e))).symm

#print axioms matching_domination_iff
#print axioms collision_free_dominator_unique
def TableChamber (p q : ℕ) (z : QPoint) : Prop :=
  z 0 = 1 ∧ ∀ c ∈ originalConstraints p q,
    LexSatisfied c.1 (c.2.map (fun r => qEval r z))

theorem table_matching_locus_iff (p q : ℕ) (π : Fin 10 ≃ Fin 10) (z : QPoint) :
    TableHolds p q π z ↔ MatchingLocus (TableChamber p q)
      (fun e z => qEval (shortForm p false e) z)
      (fun e z => qEval (shortForm q true e) z) π z := by
  simp only [TableHolds, MatchingLocus, TableChamber, matchingRows,
    qEval_sub, sub_eq_zero]
  tauto

theorem table_domination_iff (p q : ℕ) (π σ : Fin 10 ≃ Fin 10) :
    (∀ z, TableHolds p q π z → TableHolds p q σ z) ↔
    ∀ a z, TableHolds p q π z →
      qEval (shortForm p false a) z = qEval (shortForm p false (σ (π.symm a))) z := by
  simp only [table_matching_locus_iff]
  exact matching_domination_iff (TableChamber p q)
    (fun e z => qEval (shortForm p false e) z)
    (fun e z => qEval (shortForm q true e) z) π σ

#print axioms table_domination_iff
end DifferenceTableResearch
