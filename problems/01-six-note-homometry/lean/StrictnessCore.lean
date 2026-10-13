/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ExchangeCriterion
import Mathlib.Data.ZMod.Basic
import FamilyRepresentatives

namespace OnePitchShift

lemma natCast_eq_two_cases (n x y : ℕ) (hx : x < 2 * n) (hy : y < n)
    (h : (x : ZMod n) = (y : ZMod n)) : x = y ∨ x = y + n := by
  have hm := (ZMod.natCast_eq_natCast_iff' x y n).mp h
  rw [Nat.mod_eq_of_lt hy] at hm
  by_cases hxn : x < n
  · rw [Nat.mod_eq_of_lt hxn] at hm
    exact Or.inl hm
  · have hn : n ≤ x := by omega
    have hsub : x - n < n := by omega
    rw [Nat.mod_eq_sub_mod hn, Nat.mod_eq_of_lt hsub] at hm
    exact Or.inr (by omega)

/-- A finite, explicit test excluding every translation and reflection.
The hypotheses are inequalities of actual pitch representatives, not a
presupposed dihedral noncongruence statement. -/
theorem not_dihedral_of_nat_witnesses (n : ℕ) (A B : Finset ℕ)
    (hzero : 0 ∈ A)
    (hA : ∀ a ∈ A, a < n) (hB : ∀ b ∈ B, b < n)
    (ht : ∀ t ∈ B, ∃ a ∈ A, ∀ b ∈ B, a + t ≠ b ∧ a + t ≠ b + n)
    (hr : ∀ t ∈ B, ∃ a ∈ A, ∀ b ∈ B,
      n + t - a ≠ b ∧ n + t - a ≠ b + n) :
    ¬ DihedralEquivalent (A.image (fun (a : ℕ) => (a : ZMod n)))
      (B.image (fun (b : ℕ) => (b : ZMod n))) := by
  intro heq
  have hz : (0 : ZMod n) ∈ A.image (fun (a : ℕ) => (a : ZMod n)) :=
    Finset.mem_image.mpr ⟨0, hzero, Nat.cast_zero⟩
  rcases heq with ⟨t, heq⟩ | ⟨t, heq⟩
  · have htB : t ∈ B.image (fun (b : ℕ) => (b : ZMod n)) := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨0, hz, zero_add t⟩
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp htB
    subst t
    obtain ⟨a, ha, hw⟩ := ht u hu
    have him : (a : ZMod n) + (u : ZMod n) ∈
        B.image (fun (b : ℕ) => (b : ZMod n)) := by
      rw [heq]
      exact Finset.mem_image.mpr
        ⟨(a : ZMod n), Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp him
    have hcast : ((a + u : ℕ) : ZMod n) = (b : ZMod n) := by
      simpa only [Nat.cast_add] using hba.symm
    have hcases := natCast_eq_two_cases n (a + u) b
      (by have := hA a ha; have := hB u hu; omega) (hB b hb) hcast
    exact hcases.elim (hw b hb).1 (hw b hb).2
  · have htB : t ∈ B.image (fun (b : ℕ) => (b : ZMod n)) := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨0, hz, sub_zero t⟩
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp htB
    subst t
    obtain ⟨a, ha, hw⟩ := hr u hu
    have him : (u : ZMod n) - (a : ZMod n) ∈
        B.image (fun (b : ℕ) => (b : ZMod n)) := by
      rw [heq]
      exact Finset.mem_image.mpr
        ⟨(a : ZMod n), Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp him
    have hle : a ≤ n + u := by have := hA a ha; omega
    have hcast : ((n + u - a : ℕ) : ZMod n) = (b : ZMod n) := by
      rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, zero_add]
      exact hba.symm
    have hcases := natCast_eq_two_cases n (n + u - a) b
      (by have := hB u hu; omega) (hB b hb) hcast
    exact hcases.elim (hw b hb).1 (hw b hb).2

end OnePitchShift
