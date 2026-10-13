import GoldenUnitNormalization
import GoldenAttainment
import GoldenLowerEstimate
import GoldenCountMonotonic
import GoldenRigidity
import GoldenSplitBound
import GoldenNonpositiveLine
import GoldenThreshold

/-!
Checked formalization; see exact replay receipts. Assembly of the complete extremal theorem.
The root operation is abstract only to keep large proof elaboration independent
of the heavy sqrt module. The final wrapper must instantiate it with Real.sqrt,
and must instantiate M with the executable goldenThresholdIndex.
-/
namespace AlgebraicTunings

/-- Full exact maximum, attainment, and maximizer rigidity under a certified
integer threshold. No continuous/sample-bound assumptions are added to AP data. -/
theorem golden_exact_maximum_generic
    (phi : ℝ) (hphi : phi ^ 2 = phi + 1) (hphi0 : (3 : ℝ) / 2 < phi)
    (root : ℝ → ℝ) (hroot0 : ∀ x, 0 ≤ root x)
    (hrootsq : ∀ x, 0 ≤ x → (root x) ^ 2 = x)
    (B M : ℤ) (hB : 64 ≤ B) (hM : 0 ≤ M)
    (hMdepth : (5 * M * M) / 4 ≤ B)
    (hMnext : B < (5 * (M + 1) * (M + 1)) / 4) :
    let F := goldenLineCount phi M (root (5 * (M : ℝ) ^ 2 + 4 * B))
    (∃ n : ℕ, ∃ P : GoldenAP phi B n, (n : ℤ) + 1 = F) ∧
    (∀ n : ℕ, ∀ P : GoldenAP phi B n, (n : ℤ) + 1 ≤ F) ∧
    (∀ n : ℕ, ∀ P : GoldenAP phi B n, (n : ℤ) + 1 = F →
      |goldenNorm P.c P.d| = 1) := by
  let z := root (B : ℝ)
  let s := root 2
  let g := 2 * phi - 1
  let v := 2 * z / g
  let lineRoot := fun m : ℤ => root (5 * (m : ℝ) ^ 2 + 4 * B)
  let F := goldenLineCount phi M (lineRoot M)
  have hB0 : 0 ≤ B := by omega
  have hBR : (64 : ℝ) ≤ B := by exact_mod_cast hB
  have hz0 : 0 ≤ z := hroot0 _
  have hzsq : z ^ 2 = B := hrootsq _ (by linarith)
  have hz8 : 8 ≤ z := by nlinarith only [hz0, hzsq, hBR]
  have hzpos : 0 < z := by linarith
  have hs0 : 0 ≤ s := hroot0 _
  have hssq : s ^ 2 = 2 := hrootsq _ (by norm_num)
  have hs1 : 1 < s := by nlinarith only [hs0, hssq]
  have hg : 0 < g := by dsimp [g]; linarith
  have hgsq : g ^ 2 = 5 := by dsimp [g]; nlinarith only [hphi]
  have hgv : g * v = 2 * z := by
    dsimp [v]
    field_simp [ne_of_gt hg]
  have hvpos : 0 < v := div_pos (by linarith) hg
  have hvsq : 5 * v ^ 2 = 4 * B := by
    have he := congrArg (fun x : ℝ => x ^ 2) hgv
    rw [mul_pow, hgsq] at he
    nlinarith only [he, hzsq]
  have hline0 : ∀ m : ℤ, 0 ≤ lineRoot m := fun m => hroot0 _
  have hlinesq : ∀ m : ℤ, (lineRoot m) ^ 2 = 5 * (m : ℝ) ^ 2 + 4 * B := by
    intro m
    apply hrootsq
    nlinarith only [sq_nonneg (m : ℝ), hBR]
  have hm0 : 0 ≤ Int.floor v := Int.floor_nonneg.mpr (le_of_lt hvpos)
  have hmdepth := golden_floor_depth B v (le_of_lt hvpos) (le_of_eq hvsq)
  have hmM := golden_threshold_max B M (Int.floor v) hM hMnext hm0 hmdepth
  have hsmall := golden_floor_construction_count_lower phi hphi hphi0 B z s v
    (lineRoot (Int.floor v)) hzpos hzsq hs0 hssq hgv
    (hline0 _) (hlinesq _)
  have hmono := goldenLineCount_mono phi (by linarith) (Int.floor v) M B
    (lineRoot (Int.floor v)) (lineRoot M) hm0 hmM
    (hline0 _) (hline0 _) (hlinesq _) (hlinesq _)
  have hmonoR : (goldenLineCount phi (Int.floor v) (lineRoot (Int.floor v)) : ℝ) ≤ F := by
    exact_mod_cast hmono
  have hFlower : (1 + s) * z - 3 < (F : ℝ) := lt_of_lt_of_le hsmall hmonoR
  have hsz : 0 < (s - 1) * z := mul_pos (by linarith) hzpos
  have hFposR : (0 : ℝ) < F := by nlinarith only [hFlower, hsz, hz8]
  have hFpos : 0 < F := by exact_mod_cast hFposR
  have hFone : 1 ≤ F := by omega
  have hshort1 : z + 1 < (1 + s) * z - 3 := by nlinarith only [hsz, hz8]
  have hshort2 : (3 : ℝ) / 2 * z + 1 < (1 + s) * z - 3 := by nlinarith only [hsz, hz8]
  have hlong_unit : ∀ n : ℕ, ∀ P : GoldenAP phi B n,
      (1 + s) * z - 3 < (n : ℝ) + 1 → |goldenNorm P.c P.d| = 1 := by
    intro n P hlong
    let K : ℝ := (B : ℝ) / |(goldenNorm P.c P.d : ℝ)| + 1 / 4
    have hK : 0 ≤ K := by
      have hdiv := div_nonneg (by linarith : (0 : ℝ) ≤ B)
        (abs_nonneg (goldenNorm P.c P.d : ℝ))
      dsimp [K]
      linarith
    exact goldenAP_long_step_unit phi hphi B n P hB z s (root K)
      hz0 hzsq hs0 hssq (hroot0 _) (hrootsq _ hK) hlong
  change (∃ n : ℕ, ∃ P : GoldenAP phi B n, (n : ℤ) + 1 = F) ∧
    (∀ n : ℕ, ∀ P : GoldenAP phi B n, (n : ℤ) + 1 ≤ F) ∧
    (∀ n : ℕ, ∀ P : GoldenAP phi B n, (n : ℤ) + 1 = F →
      |goldenNorm P.c P.d| = 1)
  constructor
  · let n := (F - 1).toNat
    have hn : (n : ℤ) = F - 1 := Int.toNat_of_nonneg (by omega)
    have hnF : (n : ℤ) + 1 = F := by omega
    exact ⟨n, goldenCanonicalRun phi hphi hphi0 M B n (lineRoot M)
      hM hB0 (hline0 _) (hlinesq _) hMdepth (le_of_eq hnF), hnF⟩
  constructor
  · intro n P
    by_contra hnF
    have hgt : F < (n : ℤ) + 1 := lt_of_not_ge hnF
    have hgtR : (F : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hgt
    have hlong : (1 + s) * z - 3 < (n : ℝ) + 1 := lt_trans hFlower hgtR
    have hu := hlong_unit n P hlong
    let Q := P.unitNormalize hphi hu
    let m := goldenUnitM P.a P.b P.c P.d
    let b := goldenUnitK P.a P.b P.c P.d
    have hstart : 0 < goldenEval phi m b := Q.start_pos
    have hnorm : ∀ j : ℕ, j ≤ n → |goldenNorm m (b + (j : ℤ))| ≤ B := by
      intro j hj
      simpa only [Q, GoldenAP.unitNormalize, mul_zero, add_zero, mul_one, m, b]
        using Q.norm_bound j hj
    have hlast := (abs_le.mp (hnorm n le_rfl)).2
    by_cases hmneg : m ≤ 0
    · have hspan := golden_nonpositive_line_span phi hphi hphi0 m b B n z
        hmneg hz0 hzsq hstart hlast
      linarith
    · have hmnonneg : 0 ≤ m := by omega
      by_cases hmle : m ≤ M
      · have hcount := golden_unit_run_count_upper phi m b B n (lineRoot m)
          (hline0 _) (hlinesq _) hstart hlast
        have hcountmono := goldenLineCount_mono phi (by linarith) m M B
          (lineRoot m) (lineRoot M) hmnonneg hmle
          (hline0 _) (hline0 _) (hlinesq _) (hlinesq _)
        omega
      · have hdepth := golden_beyond_threshold B M m hM hMnext (by omega)
        have hspanZ := golden_split_run_span_sq m b B n hdepth hnorm
        have hspanR : (n : ℝ) ^ 2 ≤ 2 * B := by exact_mod_cast hspanZ
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hspan : (n : ℝ) ≤ (3 : ℝ) / 2 * z := by
          apply (sq_le_sq₀ hn0 (by nlinarith)).mp
          nlinarith only [hspanR, hzsq, sq_nonneg z]
        linarith
  · intro n P hEq
    have hEqR : (n : ℝ) + 1 = (F : ℝ) := by exact_mod_cast hEq
    apply hlong_unit n P
    linarith

#check @golden_exact_maximum_generic
#print axioms golden_exact_maximum_generic
end AlgebraicTunings
