import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
namespace SpacedVariance

lemma sum_fin_val (m : ℕ) : 2 * (∑ i : Fin m, (i.val : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma sum_fin_val_sq (m : ℕ) : 6 * (∑ i : Fin m, (i.val : ℝ)^2) = (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma pair_sq_sum {m : ℕ} (z : Fin m → ℝ) :
    (∑ i, ∑ j, (z j - z i)^2) =
      2 * ((m : ℝ) * (∑ i, (z i)^2) - (∑ i, z i)^2) := by
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma gap_sq {m : ℕ} (z : Fin m → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hgap : ∀ i j : Fin m, i < j → q * ((j.val : ℝ) - i.val) ≤ z j - z i)
    (i j : Fin m) : q^2 * ((j.val : ℝ) - i.val)^2 ≤ (z j - z i)^2 := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hv : (i.val : ℝ) ≤ j.val := by exact_mod_cast (Nat.le_of_lt hij)
    have hn := mul_nonneg hq (sub_nonneg.mpr hv)
    have hg := hgap i j hij
    nlinarith [sq_nonneg (z j - z i - q * ((j.val : ℝ) - i.val))]
  · simp
  · have hv : (j.val : ℝ) ≤ i.val := by exact_mod_cast (Nat.le_of_lt hji)
    have hn := mul_nonneg hq (sub_nonneg.mpr hv)
    have hg := hgap j i hji
    nlinarith [sq_nonneg (z i - z j - q * ((i.val : ℝ) - j.val))]

lemma index_pair_sum (m : ℕ) :
    6 * (∑ i : Fin m, ∑ j : Fin m, ((j.val : ℝ) - i.val)^2) =
      (m : ℝ)^2 * ((m : ℝ)^2 - 1) := by
  rw [pair_sq_sum]
  have h1 := sum_fin_val m
  have h2 := sum_fin_val_sq m
  nlinarith [sq_nonneg ((∑ i : Fin m, (i.val : ℝ)))]

/-- A sorted sequence with gaps at least `q` has the sharp denominator-free
second-moment bound. Equality holds for a centered arithmetic progression. -/
theorem spaced_second_moment {m : ℕ} (z : Fin m → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hgap : ∀ i j : Fin m, i < j → q * ((j.val : ℝ) - i.val) ≤ z j - z i) :
    q^2 * (m : ℝ) * ((m : ℝ)^2 - 1) ≤ 12 * ∑ i, (z i)^2 := by
  have hp : q^2 * (∑ i : Fin m, ∑ j : Fin m, ((j.val : ℝ) - i.val)^2) ≤
      ∑ i, ∑ j, (z j - z i)^2 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => gap_sq z q hq hgap i j
  have hi := index_pair_sum m
  rw [pair_sq_sum z] at hp
  have hscaled : q^2 * (m : ℝ)^2 * ((m : ℝ)^2 - 1) ≤
      12 * (m : ℝ) * ∑ i, (z i)^2 := by
    nlinarith [sq_nonneg (∑ i, z i)]
  rcases m with _ | m
  · simp
  · have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    nlinarith

end SpacedVariance
