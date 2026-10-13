import GoldenNormCore
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
COMPILED under Lean 4.32.2; exact statements, axiom audits, hashes, and
resource receipts accompany this module. It proves the global continuous
bound and its discrete-to-continuous bridge. Square-root parameters
are explicit so the main algebraic argument does not depend on square-root API.
No axioms, sorry, or native_decide are used.
-/

namespace AlgebraicTunings

private theorem le_of_sq_le_sq_nonneg_right (u v : ℝ)
    (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  by_contra hnot
  have hlt : v < u := lt_of_not_ge hnot
  have hp : 0 < (u - v) * (u + v) :=
    mul_pos (sub_pos.mpr hlt) (by linarith)
  nlinarith

/-- On either side of the vertex, endpoint bounds control the whole span. -/
theorem quadratic_one_sided_span_sq (C a b D : ℝ)
    (hab : a ≤ b)
    (ha : |a * (a - D)| ≤ C) (hb : |b * (b - D)| ≤ C)
    (hside : b ≤ D / 2 ∨ D / 2 ≤ a) :
    (b - a) ^ 2 ≤ 2 * C := by
  rcases abs_le.mp ha with ⟨haL, haU⟩
  rcases abs_le.mp hb with ⟨hbL, hbU⟩
  rcases hside with hleft | hright
  · have hp : 0 ≤ (b - a) * (D - 2 * b) :=
      mul_nonneg (sub_nonneg.mpr hab) (by linarith)
    nlinarith
  · have hp : 0 ≤ (b - a) * (2 * a - D) :=
      mul_nonneg (sub_nonneg.mpr hab) (by linarith)
    nlinarith

/-- The positivity-sensitive global interval bound.
Instantiate `r = sqrt C`, `s = sqrt 2` to get `(1 + sqrt 2) * sqrt C`.
The bound is proved from the full interval hypothesis, including the vertex
when it lies inside; it is not merely an endpoint-bound assertion. -/
theorem positive_quadratic_interval_bound (C a b D r s : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = C)
    (hs : 0 ≤ s) (hssq : s ^ 2 = 2)
    (hinterval : ∀ x : ℝ, a ≤ x → x ≤ b → |x * (x - D)| ≤ C) :
    b - a ≤ (1 + s) * r := by
  have haB := hinterval a le_rfl hab
  have hbB := hinterval b hab le_rfl
  have hsr : 0 ≤ s * r := mul_nonneg hs hr
  have hsrsq : (s * r) ^ 2 = 2 * C := by
    rw [mul_pow, hssq, hrsq]
  by_cases hside : b ≤ D / 2 ∨ D / 2 ≤ a
  · have hsq := quadratic_one_sided_span_sq C a b D hab haB hbB hside
    have hspan : b - a ≤ s * r :=
      le_of_sq_le_sq_nonneg_right _ _ hsr (by nlinarith [hsrsq])
    nlinarith
  · have hvA : a ≤ D / 2 := by
      by_contra hn
      exact hside (Or.inr (le_of_lt (lt_of_not_ge hn)))
    have hvB : D / 2 ≤ b := by
      by_contra hn
      exact hside (Or.inl (le_of_lt (lt_of_not_ge hn)))
    have hvBnd := (abs_le.mp (hinterval (D / 2) hvA hvB)).1
    have hDsq : D ^ 2 ≤ 4 * C := by nlinarith
    have hD : D ≤ 2 * r :=
      le_of_sq_le_sq_nonneg_right _ _ (by linarith) (by nlinarith [hrsq])
    have hb0 : 0 ≤ b := by linarith
    have hDb : D * b ≤ (2 * r) * b := mul_le_mul_of_nonneg_right hD hb0
    have hbU := (abs_le.mp hbB).2
    have hshift : (b - r) ^ 2 ≤ (s * r) ^ 2 := by
      nlinarith [hrsq, hsrsq]
    have hbr : b - r ≤ s * r :=
      le_of_sq_le_sq_nonneg_right _ _ hsr hshift
    nlinarith

/-- One interpolation cell, deriving a continuous bound from two integer samples. -/
theorem monic_quadratic_cell_bound (p q u s K : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hu : |u ^ 2 + p * u + q| ≤ K)
    (hu1 : |(u + 1) ^ 2 + p * (u + 1) + q| ≤ K) :
    |(u + s) ^ 2 + p * (u + s) + q| ≤ K + 1 / 4 := by
  rcases abs_le.mp hu with ⟨huL, huU⟩
  rcases abs_le.mp hu1 with ⟨hu1L, hu1U⟩
  have h0 : 0 ≤ 1 - s := by linarith
  have hlo0 := mul_le_mul_of_nonneg_left huL h0
  have hlo1 := mul_le_mul_of_nonneg_left hu1L hs0
  have hhi0 := mul_le_mul_of_nonneg_left huU h0
  have hhi1 := mul_le_mul_of_nonneg_left hu1U hs0
  have he0 := interpolation_error_nonneg s hs0 hs1
  have he1 := interpolation_error_le_quarter s
  rw [monic_quadratic_interpolation]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Actual discrete-to-continuous bridge on a nonnegative integer interval.
Every sample from 0 through n is required; no continuous premise is assumed. -/
theorem monic_quadratic_discrete_to_continuous (p q K : ℝ) (n : ℕ)
    (hK : 0 ≤ K)
    (hdiscrete : ∀ j : ℕ, j ≤ n → |(j : ℝ) ^ 2 + p * (j : ℝ) + q| ≤ K) :
    ∀ t : ℝ, 0 ≤ t → t ≤ (n : ℝ) →
      |t ^ 2 + p * t + q| ≤ K + 1 / 4 := by
  intro t ht0 htn
  by_cases hlast : t = (n : ℝ)
  · subst t
    exact (hdiscrete n le_rfl).trans (by linarith)
  · let j : ℕ := ⌊t⌋₊
    have hjt : (j : ℝ) ≤ t := Nat.floor_le ht0
    have htj : t < (j : ℝ) + 1 := Nat.lt_floor_add_one t
    have hjn : j < n := by
      have htn' : t < (n : ℝ) := lt_of_le_of_ne htn hlast
      exact_mod_cast (lt_of_le_of_lt hjt htn')
    have hj1n : j + 1 ≤ n := hjn
    have hjB := hdiscrete j (Nat.le_of_lt hjn)
    have hj1B := hdiscrete (j + 1) hj1n
    push_cast at hj1B
    have hcell := monic_quadratic_cell_bound p q (j : ℝ) (t - j) K
      (by linarith) (by linarith) hjB hj1B
    convert hcell using 1 <;> congr 1 <;> ring

/-- Global AP-index bound derived solely from its integer samples.
Later the golden norm factorization supplies alpha=a/d and beta=a'/d'. -/
theorem monic_discrete_positive_span_bound
    (alpha beta K r s : ℝ) (n : ℕ)
    (halpha : 0 < alpha) (hK : 0 ≤ K)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = K + 1 / 4)
    (hs : 0 ≤ s) (hssq : s ^ 2 = 2)
    (hdiscrete : ∀ j : ℕ, j ≤ n →
      |((j : ℝ) + alpha) * ((j : ℝ) + beta)| ≤ K) :
    (n : ℝ) ≤ (1 + s) * r := by
  have hpoly : ∀ j : ℕ, j ≤ n →
      |(j : ℝ) ^ 2 + (alpha + beta) * (j : ℝ) + alpha * beta| ≤ K := by
    intro j hj
    convert hdiscrete j hj using 1 <;> congr 1 <;> ring
  have hcont := monic_quadratic_discrete_to_continuous
    (alpha + beta) (alpha * beta) K n hK hpoly
  have hinterval : ∀ x : ℝ, alpha ≤ x → x ≤ alpha + (n : ℝ) →
      |x * (x - (alpha - beta))| ≤ K + 1 / 4 := by
    intro x hx0 hxn
    have ht := hcont (x - alpha) (by linarith) (by linarith)
    convert ht using 1 <;> congr 1 <;> ring
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbound := positive_quadratic_interval_bound
    (K + 1 / 4) alpha (alpha + n) (alpha - beta) r s
    halpha (by linarith) hr hrsq hs hssq hinterval
  simpa only [add_sub_cancel_left] using hbound

#check @quadratic_one_sided_span_sq
#check @positive_quadratic_interval_bound
#check @monic_quadratic_cell_bound
#check @monic_quadratic_discrete_to_continuous
#check @monic_discrete_positive_span_bound

#print axioms quadratic_one_sided_span_sq
#print axioms positive_quadratic_interval_bound
#print axioms monic_quadratic_cell_bound
#print axioms monic_quadratic_discrete_to_continuous
#print axioms monic_discrete_positive_span_bound

end AlgebraicTunings
