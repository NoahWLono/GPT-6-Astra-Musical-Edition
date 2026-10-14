import Mathlib.Tactic

open scoped BigOperators
namespace Rhythmic

/-- A partition of `[0,3*k)` into distinct-positive-gap arithmetic triplets. -/
structure PerfectTripletTiling (k : ℕ) where
  start : Fin k → ℕ
  gap : Fin k → ℕ
  gap_pos : ∀ i, 0 < gap i
  gap_injective : Function.Injective gap
  cover : (Fin k × Fin 3) ≃ Fin (3 * k)
  cover_formula : ∀ i j, (cover (i,j)).val = start i + j.val * gap i

namespace PerfectTripletTiling

variable {k : ℕ} (T : PerfectTripletTiling k)

/-- Triplets having one point in each consecutive block of length `k`. -/
def transverseIndices : Finset (Fin k) := Finset.univ.filter fun i =>
  T.start i < k ∧ k ≤ T.start i + T.gap i ∧
    T.start i + T.gap i < 2*k ∧ 2*k ≤ T.start i + 2*T.gap i

abbrev Transverse := {i : Fin k // i ∈ T.transverseIndices}

def a (i : T.Transverse) : ℤ := T.start i.val
def b (i : T.Transverse) : ℤ := (T.start i.val : ℤ) + T.gap i.val - k
def c (i : T.Transverse) : ℤ := (T.start i.val : ℤ) + 2*T.gap i.val - 2*k

lemma transverse_mem (i : T.Transverse) :
    T.start i.val < k ∧ k ≤ T.start i.val + T.gap i.val ∧
    T.start i.val + T.gap i.val < 2*k ∧ 2*k ≤ T.start i.val + 2*T.gap i.val := by
  simpa only [transverseIndices, Finset.mem_filter, Finset.mem_univ, true_and] using i.property

lemma endpoint_lt (i : Fin k) : T.start i + 2*T.gap i < 3*k := by
  have h := (T.cover (i, (2 : Fin 3))).isLt
  rw [T.cover_formula] at h
  exact h

lemma position_injective (j : Fin 3) :
    Function.Injective (fun i : Fin k => T.start i + j.val * T.gap i) := by
  intro i l h
  have he : T.cover (i,j) = T.cover (l,j) := by
    apply Fin.ext
    simpa only [T.cover_formula] using h
  exact congrArg Prod.fst (T.cover.injective he)

lemma a_injective : Function.Injective T.a := by
  intro i j h
  apply Subtype.ext
  apply T.position_injective (0 : Fin 3)
  simpa [a] using h

lemma b_injective : Function.Injective T.b := by
  intro i j h
  apply Subtype.ext
  apply T.position_injective (1 : Fin 3)
  simp only [Fin.val_one, one_mul]
  dsimp [b] at h
  exact_mod_cast (by linarith : (T.start i.val : ℤ) + T.gap i.val = T.start j.val + T.gap j.val)

lemma c_injective : Function.Injective T.c := by
  intro i j h
  apply Subtype.ext
  apply T.position_injective (2 : Fin 3)
  change T.start i.val + 2 * T.gap i.val = T.start j.val + 2 * T.gap j.val
  dsimp [c] at h
  exact_mod_cast (by linarith : (T.start i.val : ℤ) + 2*T.gap i.val = T.start j.val + 2*T.gap j.val)

lemma arithmetic (i : T.Transverse) : T.a i + T.c i = 2*T.b i := by
  dsimp [a,b,c]
  ring

lemma difference_injective : Function.Injective (fun i : T.Transverse => T.a i - T.c i) := by
  intro i j h
  apply Subtype.ext
  apply T.gap_injective
  dsimp [a,c] at h
  exact_mod_cast (by linarith : (T.gap i.val : ℤ) = T.gap j.val)

lemma a_nonneg (i : T.Transverse) : 0 ≤ T.a i := by
  dsimp [a]
  positivity

lemma a_lt (i : T.Transverse) : T.a i < k := by
  dsimp [a]
  exact_mod_cast (T.transverse_mem i).1

lemma b_nonneg (i : T.Transverse) : 0 ≤ T.b i := by
  have h : (k : ℤ) ≤ T.start i.val + T.gap i.val := by
    exact_mod_cast (T.transverse_mem i).2.1
  dsimp [b]
  linarith

lemma b_lt (i : T.Transverse) : T.b i < k := by
  have h : (T.start i.val : ℤ) + T.gap i.val < 2*k := by
    exact_mod_cast (T.transverse_mem i).2.2.1
  dsimp [b]
  linarith

lemma c_nonneg (i : T.Transverse) : 0 ≤ T.c i := by
  have h : (2 : ℤ)*k ≤ T.start i.val + 2*T.gap i.val := by
    exact_mod_cast (T.transverse_mem i).2.2.2
  dsimp [c]
  linarith

lemma c_lt (i : T.Transverse) : T.c i < k := by
  have h : (T.start i.val : ℤ) + 2*T.gap i.val < 3*k := by
    exact_mod_cast T.endpoint_lt i.val
  dsimp [c]
  linarith

/-- Apply the analytic bound to the transverse subfamily of an actual tiling.
The bound is an explicit hypothesis so this bridge is independent of its proof. -/
theorem transverse_bound_of
    (core : ∀ {k t : ℕ} (a b c : Fin t → ℤ),
      Function.Injective a → Function.Injective b → Function.Injective c →
      (∀ i, a i + c i = 2*b i) → Function.Injective (fun i => a i - c i) →
      (∀ i, 0 ≤ a i) → (∀ i, a i < k) →
      (∀ i, 0 ≤ c i) → (∀ i, c i < k) →
      (t : ℝ)^2 - 1 ≤ 3*(k : ℝ)*((k : ℝ)-t)) :
    (T.transverseIndices.card : ℝ)^2 - 1 ≤
      3*(k : ℝ)*((k : ℝ)-T.transverseIndices.card) := by
  let e : Fin (Fintype.card T.Transverse) ≃ T.Transverse := (Fintype.equivFin T.Transverse).symm
  have h := core (k := k) (T.a ∘ e) (T.b ∘ e) (T.c ∘ e)
    (T.a_injective.comp e.injective) (T.b_injective.comp e.injective)
    (T.c_injective.comp e.injective) (fun i => T.arithmetic (e i))
    (T.difference_injective.comp e.injective)
    (fun i => T.a_nonneg (e i)) (fun i => T.a_lt (e i))
    (fun i => T.c_nonneg (e i)) (fun i => T.c_lt (e i))
  simpa only [Transverse, Fintype.card_coe] using h

end PerfectTripletTiling
end Rhythmic
