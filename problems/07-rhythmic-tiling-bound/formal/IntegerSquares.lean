import SpacedVariance
import Mathlib.Tactic
import Mathlib.Data.Finset.Sort

open scoped BigOperators
namespace Rhythmic

lemma strictMono_int_gap {m : ℕ} (f : Fin m → ℤ) (hf : StrictMono f)
    (i j : Fin m) (hij : i < j) : (j.val : ℤ) - i.val ≤ f j - f i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hg : Monotone (fun x : Fin (n+1) => f x - (x.val : ℤ)) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro x
      have hh := hf (show x.castSucc < x.succ from Fin.castSucc_lt_succ)
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      omega
    have h := hg (le_of_lt hij)
    dsimp at h
    omega

lemma sum_orderEmb (s : Finset ℤ) (F : ℤ → ℝ) :
    (∑ i : Fin s.card, F (s.orderEmbOfFin rfl i)) = ∑ x ∈ s, F x := by
  have h := Finset.sum_map Finset.univ (s.orderEmbOfFin rfl).toEmbedding F
  simpa using h.symm

lemma orderEmb_real_gap (s : Finset ℤ) (c : ℝ) (i j : Fin s.card) (hij : i < j) :
    1 * ((j.val : ℝ) - i.val) ≤
      ((s.orderEmbOfFin rfl j : ℝ)-c) - ((s.orderEmbOfFin rfl i : ℝ)-c) := by
  have h := strictMono_int_gap (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl).strictMono i j hij
  have hr : (j.val : ℝ) - i.val ≤
      (s.orderEmbOfFin rfl j : ℝ) - (s.orderEmbOfFin rfl i : ℝ) := by exact_mod_cast h
  linarith

lemma sum_range_real (k : ℕ) :
    ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_range_real_sq (k : ℕ) :
    ∑ i ∈ Finset.range k, (i : ℝ)^2 = (k : ℝ) * (k - 1) * (2*k - 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_centered_interval (k : ℕ) :
    12 * (∑ i ∈ Finset.range k, ((i : ℝ) - ((k : ℝ)-1)/2)^2) =
      (k : ℝ)*((k : ℝ)^2-1) := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_range_real_sq, sum_range_real]
  try simp
  ring

lemma finset_integer_second_moment (s : Finset ℤ) (c : ℝ) :
    (s.card : ℝ) * ((s.card : ℝ)^2-1) ≤
      12 * ∑ x ∈ s, ((x : ℝ)-c)^2 := by
  have h := SpacedVariance.spaced_second_moment
    (fun i : Fin s.card => (s.orderEmbOfFin rfl i : ℝ)-c) 1 (by norm_num)
    (orderEmb_real_gap s c)
  rw [sum_orderEmb s (fun x => ((x : ℝ)-c)^2)] at h
  simpa using h

lemma injective_integer_second_moment {m : ℕ} (f : Fin m → ℤ)
    (hf : Function.Injective f) (c : ℝ) :
    (m : ℝ) * ((m : ℝ)^2-1) ≤ 12 * ∑ i, ((f i : ℝ)-c)^2 := by
  have h := finset_integer_second_moment (Finset.univ.image f) c
  rw [Finset.card_image_of_injective _ hf] at h
  rw [Finset.sum_image (fun i _ j _ h => hf h)] at h
  simpa using h

lemma bounded_integer_second_moment {k t : ℕ} (f : Fin t → ℤ)
    (hf : Function.Injective f) (hf0 : ∀ i, 0 ≤ f i) (hfk : ∀ i, f i < k) :
    t ≤ k ∧
    12 * (∑ i, ((f i : ℝ) - ((k : ℝ)-1)/2)^2) ≤
      (k : ℝ)*((k : ℝ)^2-1) -
        ((k : ℝ)-t)*(((k : ℝ)-t)^2-1) := by
  classical
  let U : Finset ℤ := (Finset.range k).image Int.ofNat
  let s : Finset ℤ := Finset.univ.image f
  have hU : U.card = k := by
    dsimp [U]
    rw [Finset.card_image_of_injective _ Int.ofNat_injective, Finset.card_range]
  have hs : s.card = t := by
    simp [s, Finset.card_image_of_injective _ hf]
  have hsub : s ⊆ U := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨(f i).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · have := hf0 i
      have := hfk i
      omega
    · exact Int.toNat_of_nonneg (hf0 i)
  have htk : t ≤ k := by
    have h := Finset.card_le_card hsub
    simpa [hU, hs] using h
  refine ⟨htk, ?_⟩
  let c : ℝ := ((k : ℝ)-1)/2
  have hmiss := finset_integer_second_moment (U \ s) c
  have hcard : (U \ s).card = k-t := by
    rw [Finset.card_sdiff_of_subset hsub, hU, hs]
  rw [hcard, Nat.cast_sub htk] at hmiss
  have hsum := Finset.sum_sdiff (f := fun x : ℤ => ((x : ℝ)-c)^2) hsub
  have htotal : 12 * ∑ x ∈ U, ((x : ℝ)-c)^2 = (k : ℝ)*((k : ℝ)^2-1) := by
    dsimp [U]
    rw [Finset.sum_image (fun i _ j _ h => Int.ofNat_injective h)]
    simpa [c] using sum_centered_interval k
  have hused : (∑ x ∈ s, ((x : ℝ)-c)^2) = ∑ i, ((f i : ℝ)-c)^2 := by
    dsimp [s]
    rw [Finset.sum_image (fun i _ j _ h => hf h)]
  rw [hused] at hsum
  dsimp [c] at hmiss hsum htotal
  linarith

theorem partial_transverse_bound_shifted {k t : ℕ} (a b c : Fin t → ℤ)
    (p : ℤ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hc : Function.Injective c) (habc : ∀ i, a i + c i = 2*b i + p)
    (hgap : Function.Injective (fun i => a i-c i))
    (ha0 : ∀ i, 0 ≤ a i) (hak : ∀ i, a i < k)
    (hc0 : ∀ i, 0 ≤ c i) (hck : ∀ i, c i < k) :
    (t : ℝ)^2-1 ≤ 3*(k : ℝ)*((k : ℝ)-t) := by
  have hA := bounded_integer_second_moment a ha ha0 hak
  have hC := bounded_integer_second_moment c hc hc0 hck
  let q : Fin t → ℤ := fun i => a i-b i
  have hq : Function.Injective q := by
    intro i j hij
    apply hgap
    have hi := habc i
    have hj := habc j
    dsimp [q] at hij
    dsimp
    omega
  have hB := injective_integer_second_moment b hb (((k : ℝ)-1-(p : ℝ))/2)
  have hQ := injective_integer_second_moment q hq ((p : ℝ)/2)
  have hid : ∀ i : Fin t,
      ((a i : ℝ)-((k : ℝ)-1)/2)^2 + ((c i : ℝ)-((k : ℝ)-1)/2)^2 =
      2*(((b i : ℝ)-((k : ℝ)-1-(p : ℝ))/2)^2 +
         ((q i : ℝ)-(p : ℝ)/2)^2) := by
    intro i
    have he : (a i : ℝ)+(c i : ℝ)=2*(b i : ℝ)+(p : ℝ) := by exact_mod_cast habc i
    have he' : (c i : ℝ)=2*(b i : ℝ)+(p : ℝ)-(a i : ℝ) := by linarith
    rw [he']
    dsimp [q]
    push_cast
    ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hid i)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hmain : 2*(t : ℝ)*((t : ℝ)^2-1) ≤
      (k : ℝ)*((k : ℝ)^2-1) -
        ((k : ℝ)-t)*(((k : ℝ)-t)^2-1) := by
    linarith [hA.2, hC.2]
  by_cases ht : t = 0
  · subst t
    simp only [Nat.cast_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_sub, sub_zero]
    nlinarith [sq_nonneg (k : ℝ)]
  · have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
    have hfactor : (t : ℝ)*((t : ℝ)^2-1-3*(k : ℝ)*((k : ℝ)-t)) ≤ 0 := by
      nlinarith [hmain]
    by_contra hn
    have hpos : 0 < (t : ℝ)*((t : ℝ)^2-1-3*(k : ℝ)*((k : ℝ)-t)) :=
      mul_pos htpos (by linarith)
    linarith

theorem partial_transverse_bound {k t : ℕ} (a b c : Fin t → ℤ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hc : Function.Injective c) (habc : ∀ i, a i + c i = 2*b i)
    (hgap : Function.Injective (fun i => a i-c i))
    (ha0 : ∀ i, 0 ≤ a i) (hak : ∀ i, a i < k)
    (hc0 : ∀ i, 0 ≤ c i) (hck : ∀ i, c i < k) :
    (t : ℝ)^2-1 ≤ 3*(k : ℝ)*((k : ℝ)-t) := by
  apply partial_transverse_bound_shifted a b c 0 ha hb hc
    (by simpa using habc) hgap ha0 hak hc0 hck

#print axioms partial_transverse_bound
end Rhythmic
