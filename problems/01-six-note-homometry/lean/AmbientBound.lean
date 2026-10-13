/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import EvenOrderRefinement
import Mathlib.Data.Fintype.Card

namespace OnePitchShift
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- In a strict one-pitch exchange, the common set, its reflected asymmetric
part, and the two endpoints occupy disjoint parts of the ambient group. -/
theorem strict_exchange_ambient_bound (C : Finset G) (d : G)
    (hzero : (0 : G) ∉ C) (hd : d ∉ C) (hdne : d ≠ 0)
    (hhom : Homometric (insert 0 C) (insert d C))
    (hstrict : ¬ DihedralEquivalent (insert 0 C) (insert d C)) :
    C.card + addOrderOf d + 2 ≤ Fintype.card G := by
  let P := asymmetricPart C d
  have hp : P.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hstrict (dihedralEquivalent_of_asymmetricPart_empty C d hempty)
  have hclosed : ∀ x ∈ P, x + d ∈ P := by
    intro x hx
    exact asymmetricPart_add_mem C d hzero hd hhom hx
  have hlo : addOrderOf d ≤ P.card := addOrderOf_le_card_of_invariant P d hp hclosed
  let RP := P.image (fun x => d - x)
  have hRPcard : RP.card = P.card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy heq
    have hh := congrArg (fun z => d - z) heq
    simpa only [sub_sub_cancel] using hh
  have hdis : Disjoint C RP := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxRP
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxRP
    have hnot : d - y ∉ C := (Finset.mem_filter.mp hy).2
    apply hnot
    rw [hyx]
    exact hxC
  have hzeroRP : (0 : G) ∉ RP := by
    intro hx
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
    have hdy : d = y := sub_eq_zero.mp heq
    apply hd
    rw [hdy]
    exact asymmetricPart_subset C d hy
  have hdRP : d ∉ RP := by
    intro hx
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
    have hh := congrArg (fun z => d - z) heq
    simp only [sub_sub_cancel, sub_self] at hh
    apply hzero
    rw [← hh]
    exact asymmetricPart_subset C d hy
  have hzU : (0 : G) ∉ C ∪ RP := by simp [hzero, hzeroRP]
  have hdU : d ∉ insert 0 (C ∪ RP) := by simp [hd, hdRP, hdne]
  have hcard : (insert d (insert 0 (C ∪ RP))).card = C.card + P.card + 2 := by
    rw [Finset.card_insert_of_notMem hdU, Finset.card_insert_of_notMem hzU,
      Finset.card_union_of_disjoint hdis, hRPcard]
  have hbound := Finset.card_le_univ (insert d (insert 0 (C ∪ RP)))
  rw [hcard] at hbound
  omega

end OnePitchShift
