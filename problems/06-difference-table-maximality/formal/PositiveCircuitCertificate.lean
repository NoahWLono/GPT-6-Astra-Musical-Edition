import Mathlib.Tactic

namespace DifferenceTableResearch

def evalRow {n : ℕ} (r z : Fin n → ℝ) : ℝ := ∑ i, r i * z i

theorem evalRow_combination {m n : ℕ}
    (c : Fin m → ℝ) (rows : Fin m → Fin n → ℝ) (z : Fin n → ℝ) :
    evalRow (fun i => ∑ j, c j * rows j i) z = ∑ j, c j * evalRow (rows j) z := by
  simp only [evalRow, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem rowspace_zero_certificate {m n : ℕ}
    (c : Fin m → ℝ) (rows : Fin m → Fin n → ℝ) (z f : Fin n → ℝ)
    (identity : f = fun i => ∑ j, c j * rows j i)
    (kernel : ∀ j, evalRow (rows j) z = 0) : evalRow f z = 0 := by
  rw [identity, evalRow_combination]
  simp [kernel]

theorem positive_pair_zero_certificate {m n : ℕ}
    (c : Fin m → ℝ) (rows : Fin m → Fin n → ℝ)
    (z f g : Fin n → ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hf : 0 ≤ evalRow f z) (hg : 0 ≤ evalRow g z)
    (identity : (fun i => a * f i + b * g i) = fun i => ∑ j, c j * rows j i)
    (kernel : ∀ j, evalRow (rows j) z = 0) :
    evalRow f z = 0 ∧ evalRow g z = 0 := by
  have zero : evalRow (fun i => a * f i + b * g i) z = 0 :=
    rowspace_zero_certificate c rows z _ identity kernel
  have balance : a * evalRow f z + b * evalRow g z = 0 := by
    simpa only [evalRow, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc] using zero
  constructor <;> nlinarith

end DifferenceTableResearch

namespace DifferenceTableResearch

def LexSatisfied (strict : Bool) : List ℝ → Prop
  | [] => strict = false
  | a :: tail => 0 < a ∨ a = 0 ∧ LexSatisfied strict tail

theorem lex_head_nonnegative (strict : Bool) (a : ℝ) (tail : List ℝ)
    (h : LexSatisfied strict (a :: tail)) : 0 ≤ a := by
  rcases h with h | ⟨h, _⟩ <;> linarith

theorem lex_zero_promotion (strict : Bool) (a : ℝ) (tail : List ℝ)
    (zero : a = 0) :
    LexSatisfied strict (a :: tail) ↔ LexSatisfied strict tail := by
  simp [LexSatisfied, zero]

theorem strict_empty_rejects : ¬LexSatisfied true [] := by
  simp [LexSatisfied]

theorem positive_head_accepts (strict : Bool) (a : ℝ) (tail : List ℝ)
    (positive : 0 < a) : LexSatisfied strict (a :: tail) := Or.inl positive

theorem pair_promotion_sound {m n : ℕ}
    (c : Fin m → ℝ) (rows : Fin m → Fin n → ℝ)
    (z f g : Fin n → ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (identity : (fun i => a * f i + b * g i) = fun i => ∑ j, c j * rows j i)
    (kernel : ∀ j, evalRow (rows j) z = 0)
    (sf sg : Bool) (tf tg : List ℝ) :
    (LexSatisfied sf (evalRow f z :: tf) ∧ LexSatisfied sg (evalRow g z :: tg)) ↔
    (evalRow f z = 0 ∧ evalRow g z = 0 ∧ LexSatisfied sf tf ∧ LexSatisfied sg tg) := by
  constructor
  · rintro ⟨hf, hg⟩
    obtain ⟨zf, zg⟩ := positive_pair_zero_certificate c rows z f g a b ha hb
      (lex_head_nonnegative sf _ tf hf) (lex_head_nonnegative sg _ tg hg) identity kernel
    exact ⟨zf, zg, (lex_zero_promotion sf _ tf zf).mp hf,
      (lex_zero_promotion sg _ tg zg).mp hg⟩
  · rintro ⟨zf, zg, hf, hg⟩
    exact ⟨(lex_zero_promotion sf _ tf zf).mpr hf,
      (lex_zero_promotion sg _ tg zg).mpr hg⟩

theorem evalRow_comm {n : ℕ} (a b : Fin n → ℝ) : evalRow a b = evalRow b a := by
  simp only [evalRow, mul_comm]

theorem evalRow_add {n : ℕ} (a b z : Fin n → ℝ) :
    evalRow (fun i => a i + b i) z = evalRow a z + evalRow b z := by
  simp [evalRow, add_mul, Finset.sum_add_distrib]

theorem evalRow_right_affine {d n : ℕ} (f w : Fin n → ℝ)
    (basis : Fin d → Fin n → ℝ) (c : Fin d → ℝ) :
    evalRow f (fun j => w j + ∑ i, c i * basis i j) =
      evalRow f w + ∑ i, c i * evalRow f (basis i) := by
  calc
    _ = evalRow w f + ∑ i, c i * evalRow (basis i) f := by
      rw [evalRow_comm, evalRow_add, evalRow_combination]
    _ = _ := by
      congr 1
      · exact evalRow_comm w f
      · apply Finset.sum_congr rfl
        intro i _
        rw [evalRow_comm]

/- Algebraic affine-fullness certificate: the producer supplies feasible points
   w and w + ε_i*basis_i, and a spanning representation for the final space.
   No topological theorem or numerical tolerance is used. -/
theorem finite_affine_hull_certificate {d n : ℕ}
    (S H : (Fin n → ℝ) → Prop) (w : Fin n → ℝ)
    (basis : Fin d → Fin n → ℝ) (eps : Fin d → ℝ)
    (base_feasible : S w)
    (perturbations_feasible : ∀ i, S (fun j => w j + eps i * basis i j))
    (eps_nonzero : ∀ i, eps i ≠ 0)
    (spanning : ∀ z, H z → ∃ c : Fin d → ℝ,
      z = fun j => w j + ∑ i, c i * basis i j)
    (f : Fin n → ℝ) (vanishes : ∀ z, S z → evalRow f z = 0) :
    ∀ z, H z → evalRow f z = 0 := by
  have base_zero := vanishes w base_feasible
  have direction_zero : ∀ i, evalRow f (basis i) = 0 := by
    intro i
    have pert_zero := vanishes _ (perturbations_feasible i)
    have linearity : evalRow f (fun j => w j + eps i * basis i j) =
        evalRow f w + eps i * evalRow f (basis i) := by
      simp [evalRow, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_assoc, mul_left_comm]
    rw [linearity, base_zero, zero_add] at pert_zero
    exact (mul_eq_zero.mp pert_zero).resolve_left (eps_nonzero i)
  intro z hz
  obtain ⟨c, rfl⟩ := spanning z hz
  rw [evalRow_right_affine, base_zero]
  simp [direction_zero]

end DifferenceTableResearch

namespace DifferenceTableResearch

/- Numeric certificate for the spanning hypothesis above. Each coordinate row
   is a combination of parameter-extraction rows and known equality rows. -/
theorem coordinate_spanning_certificate {d m n : ℕ}
    (rows : Fin m → Fin n → ℝ)
    (basis theta : Fin d → Fin n → ℝ)
    (u : Fin n → Fin m → ℝ)
    (identity : ∀ j,
      (fun k => if k = j then (1 : ℝ) else 0) =
      fun k => (∑ i, basis i j * theta i k) + ∑ r, u j r * rows r k)
    (w z : Fin n → ℝ)
    (kernel : ∀ r, evalRow (rows r) (fun k => z k - w k) = 0) :
    ∃ c : Fin d → ℝ, z = fun j => w j + ∑ i, c i * basis i j := by
  refine ⟨fun i => evalRow (theta i) (fun k => z k - w k), ?_⟩
  funext j
  have eqj : z j - w j =
      ∑ i, basis i j * evalRow (theta i) (fun k => z k - w k) := by
    calc
      _ = evalRow (fun k => if k = j then 1 else 0) (fun k => z k - w k) := by
        simp [evalRow]
      _ = evalRow (fun k => (∑ i, basis i j * theta i k) + ∑ r, u j r * rows r k)
          (fun k => z k - w k) := congrArg (fun f => evalRow f _) (identity j)
      _ = _ := by
        rw [evalRow_add, evalRow_combination, evalRow_combination]
        simp [kernel]
  have eqj' : z j - w j =
      ∑ i, evalRow (theta i) (fun k => z k - w k) * basis i j := by
    simpa only [mul_comm] using eqj
  linarith

end DifferenceTableResearch

namespace DifferenceTableResearch

theorem equal_rowspace_kernel_certificate {m k n : ℕ}
    (a : Fin m → Fin n → ℝ) (b : Fin k → Fin n → ℝ)
    (c : Fin m → Fin k → ℝ) (d : Fin k → Fin m → ℝ)
    (forward : ∀ i, a i = fun j => ∑ r, c i r * b r j)
    (backward : ∀ i, b i = fun j => ∑ r, d i r * a r j)
    (z : Fin n → ℝ) :
    (∀ i, evalRow (a i) z = 0) ↔ (∀ i, evalRow (b i) z = 0) := by
  constructor
  · intro ha i
    exact rowspace_zero_certificate (d i) a z (b i) (backward i) ha
  · intro hb i
    exact rowspace_zero_certificate (c i) b z (a i) (forward i) hb

end DifferenceTableResearch
