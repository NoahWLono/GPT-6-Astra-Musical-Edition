/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ExchangeCriterion

namespace OnePitchShift
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def translated (A : Finset G) (t : G) : Finset G := A.image (fun x => x + t)

lemma mem_translated (A : Finset G) (t x : G) :
    x + t ∈ translated A t ↔ x ∈ A := by
  simp only [translated, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact add_right_cancel heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma indicator_translated (A : Finset G) (t x : G) :
    indicator (translated A t) (x + t) = indicator A x := by
  simp only [indicator, mem_translated]

lemma translated_card (A : Finset G) (t : G) : (translated A t).card = A.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy heq
  exact add_right_cancel heq

lemma translated_insert (A : Finset G) (t a : G) :
    translated (insert a A) t = insert (a + t) (translated A t) := by
  simp only [translated, Finset.image_insert]

lemma translated_translated (A : Finset G) (t u : G) :
    translated (translated A t) u = translated A (t + u) := by
  simp only [translated, Finset.image_image, Function.comp_def, add_assoc]

lemma translated_zero (A : Finset G) : translated A 0 = A := by
  simp [translated]

lemma autocorrelation_translated (A : Finset G) (t s : G) :
    autocorrelation (translated A t) s = autocorrelation A s := by
  unfold autocorrelation translated
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    have hindex : x + t - s = (x - s) + t := by abel
    rw [hindex]
    exact indicator_translated A t (x - s)
  · intro x hx y hy heq
    exact add_right_cancel heq

theorem homometric_translated (A B : Finset G) (t : G)
    (h : Homometric A B) : Homometric (translated A t) (translated B t) := by
  intro s
  rw [autocorrelation_translated, autocorrelation_translated]
  exact h s

theorem dihedralEquivalent_translated (A B : Finset G) (t : G)
    (h : DihedralEquivalent A B) :
    DihedralEquivalent (translated A t) (translated B t) := by
  rcases h with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    refine ⟨u, ?_⟩
    rw [hu]
    simp only [translated, Finset.image_image, Function.comp_def]
    congr 1
    funext x
    abel
  · right
    refine ⟨u + t + t, ?_⟩
    rw [hu]
    simp only [translated, Finset.image_image, Function.comp_def]
    congr 1
    funext x
    abel

theorem dihedralEquivalent_translated_iff (A B : Finset G) (t : G) :
    DihedralEquivalent (translated A t) (translated B t) ↔ DihedralEquivalent A B := by
  constructor
  · intro h
    have hh := dihedralEquivalent_translated (translated A t) (translated B t) (-t) h
    simpa only [translated_translated, add_neg_cancel, translated_zero] using hh
  · exact dihedralEquivalent_translated A B t

lemma exists_insert_of_card_add_one (C A : Finset G) (hsub : C ⊆ A)
    (hcard : A.card = C.card + 1) : ∃ a, a ∉ C ∧ A = insert a C := by
  have hdiff : (A \ C).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiff
  have hmem : a ∈ A \ C := by rw [ha]; simp
  have hanot := (Finset.mem_sdiff.mp hmem).2
  refine ⟨a, hanot, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hc : x ∈ C
    · exact Finset.mem_insert_of_mem hc
    · have hh : x ∈ A \ C := Finset.mem_sdiff.mpr ⟨hx, hc⟩
      rw [ha] at hh
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hh))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (Finset.mem_sdiff.mp hmem).1
    · exact hsub hx

end OnePitchShift
