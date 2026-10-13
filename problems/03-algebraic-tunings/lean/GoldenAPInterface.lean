import GoldenIntervals
import GoldenNonzero
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
Source formalization; see the exact replay receipt for verification status. Algebraic interface for applying the discrete bound to
actual lattice progressions in Z[phi]. Norm nonvanishing is supplied by GoldenNonzero. The final explicit
square-root wrapper and extremal attainment/counting remain next steps.
-/
namespace AlgebraicTunings

def goldenEval (phi : ℝ) (a b : ℤ) : ℝ := (a : ℝ) * phi + b

/-- Evaluation takes the lattice progression to the frequency progression. -/
theorem goldenEval_progression (phi : ℝ) (a b c d k : ℤ) :
    goldenEval phi (a + k * c) (b + k * d) =
      goldenEval phi a b + (k : ℝ) * goldenEval phi c d := by
  unfold goldenEval
  push_cast
  ring

/-- The norm is the product of the two real embeddings. -/
theorem goldenNorm_real_factorization (phi : ℝ)
    (hphi : phi ^ 2 = phi + 1) (a b : ℤ) :
    goldenEval phi a b * goldenEval (1 - phi) a b = (goldenNorm a b : ℝ) := by
  unfold goldenEval goldenNorm
  push_cast
  linear_combination -((a : ℝ) ^ 2) * hphi

/-- A finite actual lattice progression, with bounds at every note. -/
structure GoldenAP (phi : ℝ) (B : ℤ) (n : ℕ) where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  start_pos : 0 < goldenEval phi a b
  step_pos : 0 < goldenEval phi c d
  norm_bound : ∀ j : ℕ, j ≤ n →
    |goldenNorm (a + (j : ℤ) * c) (b + (j : ℤ) * d)| ≤ B

/-- The normalized real polynomial agrees with the integer norm at every sample.
Nonzero conjugate-step is stated explicitly here; it will be discharged from
integrality and the irreducibility of X²-X-1, not assumed in the final theorem. -/
theorem goldenNorm_normalized_sample (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (a b c d k : ℤ)
    (hd : goldenEval phi c d ≠ 0)
    (hd' : goldenEval (1 - phi) c d ≠ 0) :
    ((k : ℝ) + goldenEval phi a b / goldenEval phi c d) *
      ((k : ℝ) + goldenEval (1 - phi) a b / goldenEval (1 - phi) c d) =
      (goldenNorm (a + k * c) (b + k * d) : ℝ) / (goldenNorm c d : ℝ) := by
  rw [← goldenNorm_real_factorization phi hphi (a + k * c) (b + k * d),
    ← goldenNorm_real_factorization phi hphi c d,
    goldenEval_progression, goldenEval_progression]
  field_simp [hd, hd']
  <;> ring

/-- Positivity of a represented frequency excludes the zero lattice element. -/
theorem goldenEval_pos_coords_ne (phi : ℝ) (a b : ℤ)
    (h : 0 < goldenEval phi a b) : a ≠ 0 ∨ b ≠ 0 := by
  by_contra hn
  push_neg at hn
  rcases hn with ⟨rfl, rfl⟩
  norm_num [goldenEval] at h

/-- The actual global norm-scale bound for every integral golden AP.
The root parameters are explicit definitions by equations, not extra geometric
hypotheses. All integer sample bounds come from P.norm_bound. -/
theorem goldenAP_global_span_bound (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (B : ℤ) (n : ℕ) (P : GoldenAP phi B n) (hB : 0 ≤ B)
    (r s : ℝ) (hr : 0 ≤ r)
    (hrsq : r ^ 2 = (B : ℝ) / |(goldenNorm P.c P.d : ℝ)| + 1 / 4)
    (hs : 0 ≤ s) (hssq : s ^ 2 = 2) :
    (n : ℝ) ≤ (1 + s) * r := by
  have hcoords := goldenEval_pos_coords_ne phi P.c P.d P.step_pos
  have hqZ := goldenNorm_abs_pos P.c P.d hcoords
  have hqR : 0 < |(goldenNorm P.c P.d : ℝ)| := by exact_mod_cast hqZ
  have hqne : (goldenNorm P.c P.d : ℝ) ≠ 0 := abs_pos.mp hqR
  have hd : goldenEval phi P.c P.d ≠ 0 := ne_of_gt P.step_pos
  have hd' : goldenEval (1 - phi) P.c P.d ≠ 0 := by
    intro hz
    have hf := goldenNorm_real_factorization phi hphi P.c P.d
    rw [hz, mul_zero] at hf
    exact hqne hf.symm
  have hBR : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hK : 0 ≤ (B : ℝ) / |(goldenNorm P.c P.d : ℝ)| :=
    div_nonneg hBR (le_of_lt hqR)
  apply monic_discrete_positive_span_bound
    (goldenEval phi P.a P.b / goldenEval phi P.c P.d)
    (goldenEval (1 - phi) P.a P.b / goldenEval (1 - phi) P.c P.d)
    ((B : ℝ) / |(goldenNorm P.c P.d : ℝ)|) r s n
    (div_pos P.start_pos P.step_pos) hK hr hrsq hs hssq
  intro j hj
  have hnormR : |(goldenNorm (P.a + (j : ℤ) * P.c)
      (P.b + (j : ℤ) * P.d) : ℝ)| ≤ (B : ℝ) := by
    exact_mod_cast P.norm_bound j hj
  have hf := goldenNorm_normalized_sample phi hphi P.a P.b P.c P.d (j : ℤ) hd hd'
  have hquot := div_le_div_of_nonneg_right hnormR (le_of_lt hqR)
  rw [← abs_div] at hquot
  rw [← hf] at hquot
  simpa only [Int.cast_natCast] using hquot

#print axioms goldenEval_progression
#print axioms goldenNorm_real_factorization
#print axioms goldenNorm_normalized_sample
#print axioms goldenEval_pos_coords_ne
#print axioms goldenAP_global_span_bound

end AlgebraicTunings
