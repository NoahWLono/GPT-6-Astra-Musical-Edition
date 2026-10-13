/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge
import ComponentConstruction
import Mathlib.Tactic.Tauto

namespace OnePitchShift

theorem three_family_homometric (q : ℕ) (hq : 5 ≤ q) :
    Homometric ((threeA q).image (fun (a : ℕ) => (a : ZMod (3 * q))))
      ((threeB q).image (fun (a : ℕ) => (a : ZMod (3 * q)))) := by
  let PN : Finset ℕ := {1, q + 1, 2 * q + 1}
  let QN : Finset ℕ := {2, q - 2}
  let P := PN.image (fun (a : ℕ) => (a : ZMod (3 * q)))
  let Q := QN.image (fun (a : ℕ) => (a : ZMod (3 * q)))
  let d : ZMod (3 * q) := (q : ℕ)
  have hPN : ∀ a ∈ PN, a < 3 * q := by
    intro a ha
    simp only [PN, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha <;> omega
  have hQN : ∀ a ∈ QN, a < 3 * q := by
    intro a ha
    simp only [QN, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha <;> omega
  have hdisN : Disjoint PN QN := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [PN, Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [QN, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases ha with ha | ha | ha <;>
      rcases hb with hb | hb <;> omega
  have hdis : Disjoint P Q := cast_images_disjoint _ PN QN hPN hQN hdisN
  have hzero : (0 : ZMod (3 * q)) ∉ P ∪ Q := by
    rw [Finset.mem_union]
    change ¬ ((0 : ZMod (3 * q)) ∈ PN.image _ ∨ (0 : ZMod (3 * q)) ∈ QN.image _)
    rw [← Nat.cast_zero (R := ZMod (3 * q)),
      cast_mem_image_iff _ PN hPN 0 (by omega), cast_mem_image_iff _ QN hQN 0 (by omega)]
    simp only [PN, QN, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hd : d ∉ P ∪ Q := by
    rw [Finset.mem_union]
    change ¬ (((q : ℕ) : ZMod (3 * q)) ∈ PN.image _ ∨
      ((q : ℕ) : ZMod (3 * q)) ∈ QN.image _)
    rw [cast_mem_image_iff _ PN hPN (q) (by omega),
      cast_mem_image_iff _ QN hQN (q) (by omega)]
    simp only [PN, QN, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hPeq : P = {1, 1 + d, 1 + d + d} := by
    have hi : ((2 * q + 1 : ℕ) : ZMod (3 * q)) = 1 + d + d := by
      rw [show 2 * q + 1 = 1 + q + q by omega]
      simp only [Nat.cast_add, Nat.cast_one, d]
    ext x
    simp only [P, PN, Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton, Nat.cast_one, hi]
    have hj : ((q + 1 : ℕ) : ZMod (3 * q)) = 1 + d := by
      simp [Nat.cast_add, d, add_comm]
    rw [hj]
  have hQeq : Q = {2, d - 2} := by
    ext x
    simp [Q, QN, d, Nat.cast_sub (show 2 ≤ q by omega)]
  have hddd : d + d + d = 0 := by
    change (q : ZMod (3 * q)) + (q : ZMod (3 * q)) + (q : ZMod (3 * q)) = 0
    rw [← Nat.cast_add, ← Nat.cast_add, show q + q + q = 3 * q by omega]
    exact ZMod.natCast_self _
  have hp : ∀ x, x + d ∈ P ↔ x ∈ P := by
    rw [hPeq]
    exact triple_periodic 1 d hddd
  have hqr : ∀ x, d - x ∈ Q ↔ x ∈ Q := by
    rw [hQeq]
    exact symmetric_pair 2 d
  have hAeq : (threeA q).image (fun (a : ℕ) => (a : ZMod (3 * q))) = insert 0 (P ∪ Q) := by
    ext x
    simp only [threeA, P, Q, PN, QN, Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Nat.cast_zero]
    tauto
  have hBeq : (threeB q).image (fun (a : ℕ) => (a : ZMod (3 * q))) = insert d (P ∪ Q) := by
    ext x
    simp only [threeB, P, Q, PN, QN, d, Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto
  rw [hAeq, hBeq]
  exact homometric_of_periodic_reflected_components P Q d hdis hp hqr hzero hd

end OnePitchShift
