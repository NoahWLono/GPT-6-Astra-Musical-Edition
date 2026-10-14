import CollisionDomination
import Mathlib.Logic.Equiv.Sum

namespace DifferenceTableResearch

def assembleFibers {E I : Type*} (block : E → I)
    (g : ∀ i, {a // block a = i} ≃ {a // block a = i}) : E ≃ E :=
  (Equiv.sigmaFiberEquiv block).symm.trans
    ((Equiv.sigmaCongrRight g).trans (Equiv.sigmaFiberEquiv block))

theorem reconstruct_fibers {E I : Type*} (block : E → I)
    (g : E ≃ E) (h : ∀ a, block (g a) = block a) :
    assembleFibers block (fun i => g.subtypeEquiv
      (fun a => by rw [h a])) = g := by
  ext a
  rfl

/- Each fiber is typically a singleton, pair, or triple. The quantified
   family below therefore has product (fiber cardinality)! elements,
   rather than all 10! edge permutations. -/
theorem maximality_from_fibers {E I X V : Type*} (C : X → Prop)
    (source target : E → X → V) (π : E ≃ E) (block : E → I)
    (collision_bound : ∀ a b,
      ForcedCollision (MatchingLocus C source target π) source a b → block a = block b)
    (reverse : ∀ g : ∀ i, {a // block a = i} ≃ {a // block a = i},
      ∀ x, MatchingLocus C source target (π.trans (assembleFibers block g)) x →
        MatchingLocus C source target π x) :
    ∀ σ : E ≃ E,
      (∀ x, MatchingLocus C source target π x → MatchingLocus C source target σ x) →
      ∀ x, MatchingLocus C source target σ x → MatchingLocus C source target π x := by
  intro σ inc
  have collisions := (matching_domination_iff C source target π σ).mp inc
  let g := π.symm.trans σ
  have hb : ∀ a, block (g a) = block a := by
    intro a
    exact (collision_bound a (σ (π.symm a)) (collisions a)).symm
  have hg := reconstruct_fibers block g hb
  have eqσ : π.trans (assembleFibers block
      (fun i => g.subtypeEquiv (fun a => by rw [hb a]))) = σ := by
    rw [hg]
    ext a
    simp [g]
  rw [← eqσ]
  exact reverse _

#print axioms maximality_from_fibers
end DifferenceTableResearch
