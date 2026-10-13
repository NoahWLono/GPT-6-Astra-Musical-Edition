import GoldenAPInterface

/-!
# Normalization by an integral golden unit

SOURCE DRAFT: not compiled or kernel-checked. This file imports the actual
lattice AP interface; its hypotheses bound the represented integer norms,
not independently supplied real polynomial samples.

No classification of units or algebraic number field machinery is needed.
-/
namespace AlgebraicTunings

/-- Irrational coordinate after division by a unit with coordinates `(c,d)`. -/
def goldenUnitM (a b c d : ℤ) : ℤ :=
  (a * d - b * c) * goldenNorm c d

/-- Rational coordinate after division by a unit with coordinates `(c,d)`. -/
def goldenUnitK (a b c d : ℤ) : ℤ :=
  (-a * c + b * c + b * d) * goldenNorm c d

theorem goldenUnit_norm_sq (c d : ℤ) (hu : |goldenNorm c d| = 1) :
    goldenNorm c d ^ 2 = 1 := by
  calc
    goldenNorm c d ^ 2 = |goldenNorm c d| ^ 2 := (sq_abs _).symm
    _ = 1 := by rw [hu]; norm_num

/-- Multiplying the normalized coordinates by the original step recovers
exactly the original integer coordinates, not merely their real values. -/
theorem goldenUnit_mul_coords (a b c d : ℤ)
    (hu : |goldenNorm c d| = 1) :
    (goldenUnitM a b c d * c + goldenUnitM a b c d * d +
        goldenUnitK a b c d * c = a) ∧
    (goldenUnitM a b c d * c + goldenUnitK a b c d * d = b) := by
  have hsq := goldenUnit_norm_sq c d hu
  constructor
  · calc
      _ = a * goldenNorm c d ^ 2 := by
        unfold goldenUnitM goldenUnitK goldenNorm
        ring
      _ = a := by rw [hsq, mul_one]
  · calc
      _ = b * goldenNorm c d ^ 2 := by
        unfold goldenUnitM goldenUnitK goldenNorm
        ring
      _ = b := by rw [hsq, mul_one]

/-- Evaluation respects multiplication of the actual integral coordinates. -/
theorem goldenEval_mul_coords (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (a b c d : ℤ) :
    goldenEval phi a b * goldenEval phi c d =
      goldenEval phi (a * c + a * d + b * c) (a * c + b * d) := by
  unfold goldenEval
  push_cast
  linear_combination ((a : ℝ) * (c : ℝ)) * hphi

/-- The explicit coordinate formula really evaluates to division by the step. -/
theorem goldenUnit_eval (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (a b c d : ℤ) (hu : |goldenNorm c d| = 1)
    (hd : goldenEval phi c d ≠ 0) :
    goldenEval phi (goldenUnitM a b c d) (goldenUnitK a b c d) =
      goldenEval phi a b / goldenEval phi c d := by
  apply (eq_div_iff hd).2
  rw [goldenEval_mul_coords phi hphi]
  obtain ⟨hm, hk⟩ := goldenUnit_mul_coords a b c d hu
  rw [hm, hk]

/-- The signed normalized norm is the original norm times the unit norm. -/
theorem goldenUnit_norm (a b c d : ℤ)
    (hu : |goldenNorm c d| = 1) :
    goldenNorm (goldenUnitM a b c d) (goldenUnitK a b c d) =
      goldenNorm a b * goldenNorm c d := by
  have hsq := goldenUnit_norm_sq c d hu
  obtain ⟨hm, hk⟩ := goldenUnit_mul_coords a b c d hu
  have hmul := goldenNorm_mul (goldenUnitM a b c d) (goldenUnitK a b c d) c d
  rw [hm, hk] at hmul
  calc
    _ = goldenNorm (goldenUnitM a b c d) (goldenUnitK a b c d) *
        goldenNorm c d ^ 2 := by rw [hsq, mul_one]
    _ = (goldenNorm (goldenUnitM a b c d) (goldenUnitK a b c d) *
        goldenNorm c d) * goldenNorm c d := by ring
    _ = goldenNorm a b * goldenNorm c d := by rw [← hmul]

/-- Division by a unit preserves the absolute integer norm. -/
theorem goldenUnit_abs_norm (a b c d : ℤ)
    (hu : |goldenNorm c d| = 1) :
    |goldenNorm (goldenUnitM a b c d) (goldenUnitK a b c d)| =
      |goldenNorm a b| := by
  rw [goldenUnit_norm a b c d hu, abs_mul, hu, mul_one]

/-- Every normalized progression note has the SAME irrational coordinate. -/
theorem goldenUnitM_progression (a b c d j : ℤ) :
    goldenUnitM (a + j * c) (b + j * d) c d = goldenUnitM a b c d := by
  unfold goldenUnitM
  ring

/-- Its rational coordinate is exactly the original normalized coordinate plus j. -/
theorem goldenUnitK_progression (a b c d j : ℤ)
    (hu : |goldenNorm c d| = 1) :
    goldenUnitK (a + j * c) (b + j * d) c d = goldenUnitK a b c d + j := by
  have hsq := goldenUnit_norm_sq c d hu
  calc
    _ = goldenUnitK a b c d + j * goldenNorm c d ^ 2 := by
      unfold goldenUnitK goldenNorm
      ring
    _ = goldenUnitK a b c d + j := by rw [hsq, mul_one]

/-- The integer norm identity at each actual AP note. -/
theorem goldenUnit_progression_abs_norm (a b c d j : ℤ)
    (hu : |goldenNorm c d| = 1) :
    |goldenNorm (goldenUnitM a b c d) (goldenUnitK a b c d + j)| =
      |goldenNorm (a + j * c) (b + j * d)| := by
  have h := goldenUnit_abs_norm (a + j * c) (b + j * d) c d hu
  rw [goldenUnitM_progression, goldenUnitK_progression a b c d j hu] at h
  exact h

/-- The real quotient identity at each actual AP note. -/
theorem goldenUnit_progression_eval (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (a b c d j : ℤ) (hu : |goldenNorm c d| = 1)
    (hd : goldenEval phi c d ≠ 0) :
    goldenEval phi (goldenUnitM a b c d) (goldenUnitK a b c d + j) =
      goldenEval phi (a + j * c) (b + j * d) / goldenEval phi c d := by
  have h := goldenUnit_eval phi hphi (a + j * c) (b + j * d) c d hu hd
  rw [goldenUnitM_progression, goldenUnitK_progression a b c d j hu] at h
  exact h

/-- Positive steps preserve and reflect positivity under normalization. -/
theorem goldenUnit_pos_iff (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (a b c d : ℤ) (hu : |goldenNorm c d| = 1)
    (hd : 0 < goldenEval phi c d) :
    (0 < goldenEval phi (goldenUnitM a b c d) (goldenUnitK a b c d)) ↔
      0 < goldenEval phi a b := by
  rw [goldenUnit_eval phi hphi a b c d hu (ne_of_gt hd)]
  exact div_pos_iff_of_pos_right hd

/-- Normalize an actual lattice progression to the same number of indices,
with integer coordinates `(m,k+j)`, positive start, step one, and the same B.
The field `norm_bound` comes directly from the original integer-coordinate
bounds. No independently postulated sample bounds are used. -/
def GoldenAP.unitNormalize {phi : ℝ} {B : ℤ} {n : ℕ}
    (P : GoldenAP phi B n) (hphi : phi ^ 2 = phi + 1)
    (hu : |goldenNorm P.c P.d| = 1) : GoldenAP phi B n where
  a := goldenUnitM P.a P.b P.c P.d
  b := goldenUnitK P.a P.b P.c P.d
  c := 0
  d := 1
  start_pos := (goldenUnit_pos_iff phi hphi P.a P.b P.c P.d hu P.step_pos).2
    P.start_pos
  step_pos := by norm_num [goldenEval]
  norm_bound := by
    intro j hj
    simpa only [mul_zero, add_zero, mul_one,
      goldenUnit_progression_abs_norm P.a P.b P.c P.d (j : ℤ) hu]
      using P.norm_bound j hj

/-- Every nonnegative-index normalized note is positive. -/
theorem GoldenAP.unitNormalize_note_pos {phi : ℝ} {B : ℤ} {n : ℕ}
    (P : GoldenAP phi B n) (hphi : phi ^ 2 = phi + 1)
    (hu : |goldenNorm P.c P.d| = 1) (j : ℕ) :
    0 < goldenEval phi (goldenUnitM P.a P.b P.c P.d)
      (goldenUnitK P.a P.b P.c P.d + (j : ℤ)) := by
  have hstart := (P.unitNormalize hphi hu).start_pos
  change 0 < goldenEval phi (goldenUnitM P.a P.b P.c P.d)
    (goldenUnitK P.a P.b P.c P.d) at hstart
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  unfold goldenEval at hstart ⊢
  push_cast
  linarith

#print axioms goldenUnit_mul_coords
#print axioms goldenUnit_eval
#print axioms goldenUnit_abs_norm
#print axioms goldenUnit_progression_abs_norm
#print axioms goldenUnit_progression_eval
#print axioms goldenUnit_pos_iff
#print axioms GoldenAP.unitNormalize
#print axioms GoldenAP.unitNormalize_note_pos

end AlgebraicTunings
