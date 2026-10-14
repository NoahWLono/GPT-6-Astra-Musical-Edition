import Mathlib.Tactic

namespace Rhythmic

/-- Same-color nonattacking queens satisfy the transverse bound. The core
variance estimate is an explicit parameter, in its translated-midpoint form. -/
theorem same_parity_queens_bound_of
    (core : ∀ {k t : ℕ} (a b c : Fin t → ℤ) (p : ℤ),
      Function.Injective a → Function.Injective b → Function.Injective c →
      (∀ i, a i + c i = 2*b i + p) → Function.Injective (fun i => a i - c i) →
      (∀ i, 0 ≤ a i) → (∀ i, a i < k) →
      (∀ i, 0 ≤ c i) → (∀ i, c i < k) →
      (t : ℝ)^2 - 1 ≤ 3*(k : ℝ)*((k : ℝ)-t))
    {k t : ℕ} (a c : Fin t → ℤ) (p : ℤ)
    (ha : Function.Injective a) (hc : Function.Injective c)
    (hsum : Function.Injective (fun i => a i + c i))
    (hdiff : Function.Injective (fun i => a i - c i))
    (hparity : ∀ i, (a i + c i) % 2 = p)
    (ha0 : ∀ i, 0 ≤ a i) (hak : ∀ i, a i < k)
    (hc0 : ∀ i, 0 ≤ c i) (hck : ∀ i, c i < k) :
    (t : ℝ)^2 - 1 ≤ 3*(k : ℝ)*((k : ℝ)-t) := by
  let b : Fin t → ℤ := fun i => (a i + c i) / 2
  have hb : Function.Injective b := by
    intro i j hij
    apply hsum
    change a i + c i = a j + c j
    have hi := hparity i
    have hj := hparity j
    dsimp [b] at hij
    omega
  have heq : ∀ i, a i + c i = 2*b i + p := by
    intro i
    have hi := hparity i
    dsimp [b]
    omega
  exact core a b c p ha hb hc heq hdiff ha0 hak hc0 hck

/-- A color need not be supplied explicitly: a common remainder suffices. -/
theorem monochromatic_queens_bound_of
    (core : ∀ {k t : ℕ} (a b c : Fin t → ℤ) (p : ℤ),
      Function.Injective a → Function.Injective b → Function.Injective c →
      (∀ i, a i + c i = 2*b i + p) → Function.Injective (fun i => a i - c i) →
      (∀ i, 0 ≤ a i) → (∀ i, a i < k) →
      (∀ i, 0 ≤ c i) → (∀ i, c i < k) →
      (t : ℝ)^2 - 1 ≤ 3*(k : ℝ)*((k : ℝ)-t))
    {k t : ℕ} (a c : Fin t → ℤ)
    (ha : Function.Injective a) (hc : Function.Injective c)
    (hsum : Function.Injective (fun i => a i + c i))
    (hdiff : Function.Injective (fun i => a i - c i))
    (hparity : ∃ p : ℤ, ∀ i, (a i + c i) % 2 = p)
    (ha0 : ∀ i, 0 ≤ a i) (hak : ∀ i, a i < k)
    (hc0 : ∀ i, 0 ≤ c i) (hck : ∀ i, c i < k) :
    (t : ℝ)^2 - 1 ≤ 3*(k : ℝ)*((k : ℝ)-t) := by
  obtain ⟨p, hp⟩ := hparity
  exact same_parity_queens_bound_of core a c p ha hc hsum hdiff hp ha0 hak hc0 hck

end Rhythmic
