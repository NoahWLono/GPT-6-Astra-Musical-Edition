import BassPredicateEquiv
import Mathlib.SetTheory.Cardinal.Finite
/-! Semantic Nat.card avoids elaborating executable Fintype filters.
All types counted here are finite: their ambient types are products of Fin 12. -/
namespace Omnibus
set_option maxHeartbeats 20000

theorem semantic_cardinality_factor_twelve (P : Chord → Prop)
    (hP : ∀ k c, bounded c = true → (P (translate k c) ↔ P c)) :
    Nat.card {c : PCChord // P (unpackChord c)} =
      12 * Nat.card {t : PCTriple // P (unpackZero t)} := by
  calc
    _ = Nat.card (Fin 12 × {t : PCTriple // P (unpackZero t)}) :=
      Nat.card_congr (predicateBassEquiv P hP)
    _ = _ := by rw [Nat.card_prod,Nat.card_fin]

theorem semantic_image_factor_twelve :
    Nat.card {c : PCChord // inImage (unpackChord c) = true} =
      12 * Nat.card {t : PCTriple // inImage (unpackZero t) = true} := by
  exact semantic_cardinality_factor_twelve (fun c => inImage c = true) (by
    intro k c hc
    rw [image_translation])

theorem semantic_approachable_factor_twelve :
    Nat.card {c : PCChord // chord (unpackChord c) = true ∧ inImage (unpackChord c) = true} =
      12 * Nat.card {t : PCTriple // chord (unpackZero t) = true ∧ inImage (unpackZero t) = true} := by
  exact semantic_cardinality_factor_twelve (fun c => chord c = true ∧ inImage c = true) (by
    intro k c hc
    rw [chord_translation k c hc,image_translation])

#print axioms semantic_cardinality_factor_twelve
#print axioms semantic_image_factor_twelve
#print axioms semantic_approachable_factor_twelve
end Omnibus
