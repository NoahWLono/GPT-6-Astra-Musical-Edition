/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ExchangeCriterion

namespace OnePitchShift
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma indicator_union_of_disjoint (P Q : Finset G) (hdis : Disjoint P Q) (x : G) :
    indicator (P ∪ Q) x = indicator P x + indicator Q x := by
  have hn : ¬ (x ∈ P ∧ x ∈ Q) := by
    intro h
    exact Finset.disjoint_left.mp hdis h.1 h.2
  by_cases hp : x ∈ P <;> by_cases hq : x ∈ Q <;>
    simp_all [indicator]

theorem homometric_of_periodic_reflected_components (P Q : Finset G) (d : G)
    (hdis : Disjoint P Q)
    (hp : ∀ x, x + d ∈ P ↔ x ∈ P)
    (hq : ∀ x, d - x ∈ Q ↔ x ∈ Q)
    (hzero : (0 : G) ∉ P ∪ Q) (hd : d ∉ P ∪ Q) :
    Homometric (insert 0 (P ∪ Q)) (insert d (P ∪ Q)) := by
  apply (homometric_insert_iff_periodic (P ∪ Q) d hzero hd).mpr
  intro x
  have hpi : ∀ y, indicator P (y + d) = indicator P y := by
    intro y
    simp only [indicator, hp]
  have hqi : ∀ y, indicator Q (d - y) = indicator Q y := by
    intro y
    simp only [indicator, hq]
  have hindex : (d - (x + d)) + d = d - x := by abel
  have hpr := hpi (d - (x + d))
  rw [hindex] at hpr
  simp only [reflectionDefect, indicator_union_of_disjoint P Q hdis, hqi, hpi]
  omega

lemma pair_periodic (p d : G) (hd : d + d = 0) :
    ∀ x, x + d ∈ ({p, p + d} : Finset G) ↔ x ∈ ({p, p + d} : Finset G) := by
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right
      have := congrArg (fun y => y + d) h
      simpa only [add_assoc, hd, add_zero] using this
    · left
      exact add_right_cancel h
  · rintro (rfl | rfl)
    · exact Or.inr rfl
    · left
      rw [add_assoc, hd, add_zero]

lemma triple_periodic (p d : G) (hd : d + d + d = 0) :
    ∀ x, x + d ∈ ({p, p + d, p + d + d} : Finset G) ↔
      x ∈ ({p, p + d, p + d + d} : Finset G) := by
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · right; right
      have hh := congrArg (fun y => y + d + d) h
      have hi : x + d + d + d = x := by
        calc
          x + d + d + d = x + (d + d + d) := by abel
          _ = x := by rw [hd, add_zero]
      rw [hi] at hh
      exact hh
    · left
      exact add_right_cancel h
    · right; left
      exact add_right_cancel h
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · left
      calc
        p + d + d + d = p + (d + d + d) := by abel
        _ = p := by rw [hd, add_zero]

lemma symmetric_pair (r d : G) :
    ∀ x, d - x ∈ ({r, d - r} : Finset G) ↔ x ∈ ({r, d - r} : Finset G) := by
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right
      have := congrArg (fun y => d - y) h
      simpa only [sub_sub_cancel] using this
    · left
      have := congrArg (fun y => d - y) h
      simpa only [sub_sub_cancel] using this
  · rintro (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (sub_sub_cancel d r)

lemma symmetric_triple (r u : G) :
    ∀ x, (r + r) - x ∈ ({r - u, r, r + u} : Finset G) ↔
      x ∈ ({r - u, r, r + u} : Finset G) := by
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hi : ∀ y, (r + r) - ((r + r) - y) = y := fun y => sub_sub_cancel _ _
  have h1 : (r + r) - (r - u) = r + u := by abel
  have h2 : (r + r) - r = r := by abel
  have h3 : (r + r) - (r + u) = r - u := by abel
  constructor
  · rintro (h | h | h)
    · right; right
      have hh := congrArg (fun y => (r + r) - y) h
      rwa [hi, h1] at hh
    · right; left
      have hh := congrArg (fun y => (r + r) - y) h
      rwa [hi, h2] at hh
    · left
      have hh := congrArg (fun y => (r + r) - y) h
      rwa [hi, h3] at hh
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h2)
    · exact Or.inl h3

end OnePitchShift
