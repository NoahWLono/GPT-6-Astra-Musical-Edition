/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace OnePitchShift

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Integer-valued indicator, allowing subtraction without truncated arithmetic. -/
def indicator (C : Finset G) (x : G) : ℤ := if x ∈ C then 1 else 0

/-- The directed difference multiplicity, evaluated using one finite sum. -/
def autocorrelation (C : Finset G) (t : G) : ℤ :=
  ∑ x ∈ C, indicator C (x - t)

/-- Equality of the actual finite-set directed difference multiplicities. -/
def Homometric (A B : Finset G) : Prop :=
  ∀ t, autocorrelation A t = autocorrelation B t

/-- Equivalence by a translation or an inversion followed by translation. -/
def DihedralEquivalent (A B : Finset G) : Prop :=
  (∃ t : G, B = A.image (fun x => x + t)) ∨
  (∃ t : G, B = A.image (fun x => t - x))

/-- The part of a common chord not retained by the exchange reflection. -/
def asymmetricPart (C : Finset G) (d : G) : Finset G :=
  C.filter (fun x => d - x ∉ C)

/-- Difference from the reflection exchanging the two replaced pitches. -/
def reflectionDefect (C : Finset G) (d x : G) : ℤ :=
  indicator C x - indicator C (d - x)

lemma indicator_insert (C : Finset G) (a : G) (ha : a ∉ C) (x : G) :
    indicator (insert a C) x = indicator C x + if x = a then 1 else 0 := by
  by_cases hxa : x = a
  · subst x
    simp [indicator, ha]
  · by_cases hx : x ∈ C <;> simp [indicator, hxa, hx]

/-- The precise cancellation identity for adjoining one new pitch. -/
theorem autocorrelation_insert (C : Finset G) (a : G) (ha : a ∉ C) (t : G) :
    autocorrelation (insert a C) t =
      autocorrelation C t + indicator C (a + t) + indicator C (a - t) +
        (if t = 0 then 1 else 0) := by
  unfold autocorrelation
  rw [Finset.sum_insert ha]
  simp_rw [indicator_insert C a ha]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ x ∈ C, (if x - t = a then (1 : ℤ) else 0)) =
      indicator C (a + t) := by
    simp [indicator, sub_eq_iff_eq_add]
  rw [hsum]
  have hzero : (if a - t = a then (1 : ℤ) else 0) =
      (if t = 0 then 1 else 0) := by
    simp
  rw [hzero]
  abel

/-- Exact homometry criterion for a one-pitch exchange in a finite set.
The ambient group need not be finite for this identity. -/
theorem homometric_insert_iff_periodic (C : Finset G) (d : G)
    (hzero : (0 : G) ∉ C) (hd : d ∉ C) :
    Homometric (insert 0 C) (insert d C) ↔
      ∀ x, reflectionDefect C d (x + d) = reflectionDefect C d x := by
  constructor
  · intro h x
    have hx := h x
    rw [autocorrelation_insert C 0 hzero,
      autocorrelation_insert C d hd] at hx
    simp only [zero_add, zero_sub] at hx
    have hindex : d - (d + x) = -x := by abel
    simp only [reflectionDefect, hindex, add_comm x d]
    omega
  · intro h x
    have hx := h x
    have hindex : d - (d + x) = -x := by abel
    simp only [reflectionDefect, hindex, add_comm x d] at hx
    rw [autocorrelation_insert C 0 hzero,
      autocorrelation_insert C d hd]
    simp only [zero_add, zero_sub]
    omega

lemma reflectionDefect_eq_one_iff (C : Finset G) (d x : G) :
    reflectionDefect C d x = 1 ↔ x ∈ asymmetricPart C d := by
  by_cases hx : x ∈ C <;> by_cases hr : d - x ∈ C <;>
    simp [reflectionDefect, indicator, asymmetricPart, hx, hr]

/-- A homometric exchange makes the asymmetric component translation invariant. -/
theorem asymmetricPart_add_mem (C : Finset G) (d : G)
    (hzero : (0 : G) ∉ C) (hd : d ∉ C)
    (hhom : Homometric (insert 0 C) (insert d C))
    {x : G} (hx : x ∈ asymmetricPart C d) :
    x + d ∈ asymmetricPart C d := by
  apply (reflectionDefect_eq_one_iff C d (x + d)).mp
  rw [(homometric_insert_iff_periodic C d hzero hd).mp hhom x]
  exact (reflectionDefect_eq_one_iff C d x).mpr hx

lemma asymmetricPart_subset (C : Finset G) (d : G) :
    asymmetricPart C d ⊆ C := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- An empty asymmetric component makes the exchange an ordinary reflection. -/
theorem dihedralEquivalent_of_asymmetricPart_empty (C : Finset G) (d : G)
    (hempty : asymmetricPart C d = ∅) :
    DihedralEquivalent (insert 0 C) (insert d C) := by
  have hreflect : ∀ x ∈ C, d - x ∈ C := by
    intro x hx
    by_contra hr
    have hp : x ∈ asymmetricPart C d := Finset.mem_filter.mpr ⟨hx, hr⟩
    rw [hempty] at hp
    simp at hp
  have himage : C.image (fun x => d - x) = C := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hreflect y hy
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨d - x, hreflect x hx, ?_⟩
      abel
  right
  refine ⟨d, ?_⟩
  simp [Finset.image_insert, himage]

/-- A finite translation-invariant set contains the entire orbit of each point. -/
lemma orbit_mem_of_add_mem (P : Finset G) (d : G)
    (hclosed : ∀ x ∈ P, x + d ∈ P) {x : G} (hx : x ∈ P) :
    ∀ j : ℕ, x + j • d ∈ P := by
  intro j
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have h := hclosed (x + j • d) ih
    simpa [succ_nsmul, add_assoc] using h

/-- The additive order is bounded by the cardinality of any nonempty invariant set. -/
theorem addOrderOf_le_card_of_invariant (P : Finset G) (d : G)
    (hne : P.Nonempty) (hclosed : ∀ x ∈ P, x + d ∈ P) :
    addOrderOf d ≤ P.card := by
  obtain ⟨x, hx⟩ := hne
  apply Finset.le_card_of_inj_on_range (fun j : ℕ => x + j • d)
  · intro j hj
    exact orbit_mem_of_add_mem P d hclosed hx j
  · intro i hi j hj hij
    have hsmul : i • d = j • d := add_left_cancel hij
    exact nsmul_injOn_Iio_addOrderOf hi hj hsmul

lemma image_add_eq_of_closed (P : Finset G) (d : G)
    (hclosed : ∀ x ∈ P, x + d ∈ P) :
    P.image (fun x => x + d) = P := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hclosed x hx
  · rw [Finset.card_image_of_injective P (fun _ _ h => add_right_cancel h)]

/-- The substantive sparsity obstruction: a strict one-point exchange has order
strictly less than the size of its common part. -/
theorem strict_exchange_addOrderOf_lt_card (C : Finset G) (d : G)
    (hzero : (0 : G) ∉ C) (hd : d ∉ C)
    (hhom : Homometric (insert 0 C) (insert d C))
    (hstrict : ¬ DihedralEquivalent (insert 0 C) (insert d C)) :
    addOrderOf d < C.card := by
  let P := asymmetricPart C d
  have hne : P.Nonempty := by
    by_contra h
    have hempty : asymmetricPart C d = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    exact hstrict (dihedralEquivalent_of_asymmetricPart_empty C d hempty)
  have hclosed : ∀ x ∈ P, x + d ∈ P := by
    intro x hx
    exact asymmetricPart_add_mem C d hzero hd hhom hx
  have horder : addOrderOf d ≤ P.card :=
    addOrderOf_le_card_of_invariant P d hne hclosed
  have hsub : P ⊆ C := asymmetricPart_subset C d
  have hcard : P.card ≤ C.card := Finset.card_le_card hsub
  have hle : addOrderOf d ≤ C.card := horder.trans hcard
  apply lt_of_le_of_ne hle
  intro heq
  have hPC : P = C := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hCclosed : ∀ x ∈ C, x + d ∈ C := by
    simpa only [hPC] using hclosed
  have himage : C.image (fun x => x + d) = C := image_add_eq_of_closed C d hCclosed
  apply hstrict
  left
  refine ⟨d, ?_⟩
  simp [Finset.image_insert, himage]

/-- A strict exchange between k-note chords has exchanged order at most k-2. -/
theorem strict_exchange_order_bound [Finite G] (C : Finset G) (d : G)
    (hzero : (0 : G) ∉ C) (hd : d ∉ C) (hdne : d ≠ 0)
    (hhom : Homometric (insert 0 C) (insert d C))
    (hstrict : ¬ DihedralEquivalent (insert 0 C) (insert d C)) :
    2 ≤ addOrderOf d ∧ addOrderOf d ≤ (insert 0 C).card - 2 := by
  have hlt := strict_exchange_addOrderOf_lt_card C d hzero hd hhom hstrict
  have hpos : 0 < addOrderOf d := addOrderOf_pos d
  have hne : addOrderOf d ≠ 1 := by
    intro h
    exact hdne (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hcard : (insert 0 C).card = C.card + 1 := Finset.card_insert_of_notMem hzero
  omega

/-- In particular, the exchanged order for six notes is two, three, or four. -/
theorem strict_six_note_exchange_orders [Finite G] (C : Finset G) (d : G)
    (hzero : (0 : G) ∉ C) (hd : d ∉ C) (hdne : d ≠ 0)
    (hcard : C.card = 5)
    (hhom : Homometric (insert 0 C) (insert d C))
    (hstrict : ¬ DihedralEquivalent (insert 0 C) (insert d C)) :
    addOrderOf d = 2 ∨ addOrderOf d = 3 ∨ addOrderOf d = 4 := by
  obtain ⟨hlo, hhi⟩ := strict_exchange_order_bound C d hzero hd hdne hhom hstrict
  rw [Finset.card_insert_of_notMem hzero, hcard] at hhi
  omega

end OnePitchShift
