/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ExchangeCriterion
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity

namespace OnePitchShift

/-- A finite fixed-point-free involution pairs off its domain. -/
lemma even_card_of_fixedPointFree_involution {α : Type*} [DecidableEq α]
    (S : Finset α) (τ : α → α)
    (hclosed : ∀ x ∈ S, τ x ∈ S)
    (hinvol : ∀ x ∈ S, τ (τ x) = x)
    (hnofix : ∀ x ∈ S, τ x ≠ x) : Even S.card := by
  revert hclosed hinvol hnofix
  refine S.strongInductionOn ?_
  intro S ih hclosed hinvol hnofix
  by_cases hempty : S = ∅
  · simp [hempty]
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hb : τ a ∈ S := hclosed a ha
  have hba : τ a ≠ a := hnofix a ha
  let T := (S.erase a).erase (τ a)
  have hTsub : T ⊆ S := by
    intro x hx
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
  have hTlt : T ⊂ S :=
    lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset ha)
  have hTclosed : ∀ x ∈ T, τ x ∈ T := by
    intro x hx
    have hxS := hTsub hx
    have hxB : x ≠ τ a := (Finset.mem_erase.mp hx).1
    have hxA : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      have hh := congrArg τ heq
      rw [hinvol x hxS, hinvol a ha] at hh
      exact hxA hh
    · apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hh := congrArg τ heq
        rw [hinvol x hxS] at hh
        exact hxB hh
      · exact hclosed x hxS
  have hTeven : Even T.card := ih T hTlt hTclosed
    (fun x hx => hinvol x (hTsub hx))
    (fun x hx => hnofix x (hTsub hx))
  have hb' : τ a ∈ S.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
  have hca := Finset.card_erase_add_one ha
  have hcb := Finset.card_erase_add_one hb'
  obtain ⟨k, hk⟩ := hTeven
  refine ⟨k + 1, ?_⟩
  change ((S.erase a).erase (τ a)).card = k + k at hk
  omega

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Finite G]

/-- An invariant set has even cardinality if its translation has even order. -/
lemma even_card_of_even_translation_order (P : Finset G) (d : G)
    (hm : Even (addOrderOf d))
    (hclosed : ∀ x ∈ P, x + d ∈ P) : Even P.card := by
  obtain ⟨j, hj⟩ := hm
  have hpos := addOrderOf_pos d
  have hjpos : 0 < j := by omega
  have hjlt : j < addOrderOf d := by omega
  let e := j • d
  have he2 : e + e = 0 := by
    dsimp [e]
    rw [← add_nsmul, ← hj, addOrderOf_nsmul_eq_zero]
  have hene : e ≠ 0 := by
    intro hz
    have hdvd : addOrderOf d ∣ j := addOrderOf_dvd_of_nsmul_eq_zero hz
    have hle := Nat.le_of_dvd hjpos hdvd
    omega
  apply even_card_of_fixedPointFree_involution P (fun x => x + e)
  · intro x hx
    exact orbit_mem_of_add_mem P d hclosed hx j
  · intro x hx
    simp [add_assoc, he2]
  · intro x hx hfix
    apply hene
    have heq : x + e = x + 0 := by simpa using hfix
    exact add_left_cancel heq

/-- For an odd common part and an even exchange order, homometry forces a
reflection fixed point in the common part. -/
theorem exists_half_exchange_of_odd_common_part (C : Finset G) (d : G)
    (hzero : (0 : G) ∉ C) (hd : d ∉ C)
    (hhom : Homometric (insert 0 C) (insert d C))
    (hodd : Odd C.card) (heven : Even (addOrderOf d)) :
    ∃ r ∈ C, (2 : ℕ) • r = d := by
  classical
  let P := asymmetricPart C d
  let Q := C.filter (fun x => d - x ∈ C)
  have hPeven : Even P.card := even_card_of_even_translation_order P d heven
    (fun x hx => asymmetricPart_add_mem C d hzero hd hhom hx)
  have hsplit : Q.card + P.card = C.card := by
    simpa [Q, P, asymmetricPart] using
      Finset.card_filter_add_card_filter_not (s := C) (p := fun x => d - x ∈ C)
  by_contra hnone
  have hQclosed : ∀ x ∈ Q, d - x ∈ Q := by
    intro x hx
    obtain ⟨hxC, hrC⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hrC, ?_⟩
    simpa using hxC
  have hQeven : Even Q.card := by
    apply even_card_of_fixedPointFree_involution Q (fun x => d - x) hQclosed
    · intro x hx
      abel
    · intro x hx heq
      apply hnone
      refine ⟨x, (Finset.mem_filter.mp hx).1, ?_⟩
      rw [two_nsmul]
      have h : d = x + x := by
        calc
          d = (d - x) + x := by abel
          _ = x + x := by rw [heq]
      exact h.symm
  obtain ⟨u, hu⟩ := hPeven
  obtain ⟨v, hv⟩ := hQeven
  obtain ⟨w, hw⟩ := hodd
  omega

/-- If twice an element has even order, that element has exactly twice its order. -/
lemma addOrderOf_eq_twice_of_even_double (r : G)
    (heven : Even (addOrderOf ((2 : ℕ) • r))) :
    addOrderOf r = 2 * addOrderOf ((2 : ℕ) • r) := by
  have hformula : addOrderOf ((2 : ℕ) • r) =
      addOrderOf r / Nat.gcd (addOrderOf r) 2 := addOrderOf_nsmul r
  have hg := Nat.gcd_dvd_right (addOrderOf r) 2
  have hcases : Nat.gcd (addOrderOf r) 2 = 1 ∨
      Nat.gcd (addOrderOf r) 2 = 2 := (Nat.dvd_prime Nat.prime_two).mp hg
  rcases hcases with hone | htwo
  · rw [hone, Nat.div_one] at hformula
    have he : 2 ∣ addOrderOf r := by
      rw [← hformula]
      exact even_iff_two_dvd.mp heven
    have hbad := Nat.dvd_gcd he (dvd_refl 2)
    rw [hone] at hbad
    omega
  · have hdiv : 2 ∣ addOrderOf r := by
      simpa [htwo] using Nat.gcd_dvd_left (addOrderOf r) 2
    rw [hformula, htwo, Nat.mul_comm 2]
    exact (Nat.div_mul_cancel hdiv).symm

/-- The cyclic divisibility refinement, with genuine homometry hypotheses. -/
theorem twice_exchange_order_dvd_modulus (n : ℕ) [NeZero n]
    (C : Finset (ZMod n)) (d : ZMod n)
    (hzero : (0 : ZMod n) ∉ C) (hd : d ∉ C)
    (hhom : Homometric (insert 0 C) (insert d C))
    (hodd : Odd C.card) (heven : Even (addOrderOf d)) :
    2 * addOrderOf d ∣ n := by
  obtain ⟨r, hr, hdouble⟩ :=
    exists_half_exchange_of_odd_common_part C d hzero hd hhom hodd heven
  have hrorder : addOrderOf r = 2 * addOrderOf d := by
    simpa [hdouble] using addOrderOf_eq_twice_of_even_double r (by simpa [hdouble] using heven)
  have hdiv : addOrderOf r ∣ n := by
    simpa [ZMod.card] using (addOrderOf_dvd_card (x := r))
  rwa [hrorder] at hdiv

/-- Arithmetic necessity in the six-note theorem, excluding the small-modulus
lower bound (which will be handled separately). -/
theorem six_note_modulus_necessary (n : ℕ) [NeZero n]
    (C : Finset (ZMod n)) (d : ZMod n)
    (hzero : (0 : ZMod n) ∉ C) (hd : d ∉ C) (hdne : d ≠ 0)
    (hcard : C.card = 5)
    (hhom : Homometric (insert 0 C) (insert d C))
    (hstrict : ¬ DihedralEquivalent (insert 0 C) (insert d C)) :
    3 ∣ n ∨ 4 ∣ n := by
  have hodd : Odd C.card := by rw [hcard]; decide
  rcases strict_six_note_exchange_orders C d hzero hd hdne hcard hhom hstrict with h2 | h3 | h4
  · right
    have hdiv := twice_exchange_order_dvd_modulus n C d hzero hd hhom hodd (by rw [h2]; decide)
    simpa [h2] using hdiv
  · left
    have hdiv : addOrderOf d ∣ n := by
      simpa [ZMod.card] using (addOrderOf_dvd_card (x := d))
    rwa [h3] at hdiv
  · right
    have hdiv := twice_exchange_order_dvd_modulus n C d hzero hd hhom hodd (by rw [h4]; decide)
    have h8 : 8 ∣ n := by simpa [h4] using hdiv
    exact dvd_trans (by decide : 4 ∣ 8) h8

end OnePitchShift
