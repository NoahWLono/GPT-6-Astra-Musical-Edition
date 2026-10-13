/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge
import ComponentConstruction
import Mathlib.Tactic.Tauto

namespace OnePitchShift

theorem four_family_homometric (q : ℕ) (hq : 3 ≤ q) :
    Homometric ((fourA q).image (fun (a : ℕ) => (a : ZMod (4 * q))))
      ((fourB q).image (fun (a : ℕ) => (a : ZMod (4 * q)))) := by
  let PN : Finset ℕ := {1, 2 * q + 1}
  let QN : Finset ℕ := {q - 1, q, q + 1}
  let P := PN.image (fun (a : ℕ) => (a : ZMod (4 * q)))
  let Q := QN.image (fun (a : ℕ) => (a : ZMod (4 * q)))
  let d : ZMod (4 * q) := (2 * q : ℕ)
  have hPN : ∀ a ∈ PN, a < 4 * q := by
    intro a ha
    simp only [PN, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha <;> omega
  have hQN : ∀ a ∈ QN, a < 4 * q := by
    intro a ha
    simp only [QN, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha <;> omega
  have hdisN : Disjoint PN QN := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [PN, Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [QN, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases ha with ha | ha <;>
      rcases hb with hb | hb | hb <;> omega
  have hdis : Disjoint P Q := cast_images_disjoint _ PN QN hPN hQN hdisN
  have hzero : (0 : ZMod (4 * q)) ∉ P ∪ Q := by
    rw [Finset.mem_union]
    change ¬ ((0 : ZMod (4 * q)) ∈ PN.image _ ∨ (0 : ZMod (4 * q)) ∈ QN.image _)
    rw [← Nat.cast_zero (R := ZMod (4 * q)),
      cast_mem_image_iff _ PN hPN 0 (by omega), cast_mem_image_iff _ QN hQN 0 (by omega)]
    simp only [PN, QN, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hd : d ∉ P ∪ Q := by
    rw [Finset.mem_union]
    change ¬ (((2 * q : ℕ) : ZMod (4 * q)) ∈ PN.image _ ∨
      ((2 * q : ℕ) : ZMod (4 * q)) ∈ QN.image _)
    rw [cast_mem_image_iff _ PN hPN (2 * q) (by omega),
      cast_mem_image_iff _ QN hQN (2 * q) (by omega)]
    simp only [PN, QN, Finset.mem_insert, Finset.mem_singleton]
    omega
  let r : ZMod (4 * q) := q
  have hPeq : P = {1, 1 + d} := by
    ext x
    simp [P, PN, d, Nat.cast_add, add_comm]
  have hQeq : Q = {r - 1, r, r + 1} := by
    ext x
    simp [Q, QN, r, Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_add]
  have hdd : d + d = 0 := by
    change ((2 * q : ℕ) : ZMod (4 * q)) + ((2 * q : ℕ) : ZMod (4 * q)) = 0
    rw [← Nat.cast_add, show 2 * q + 2 * q = 4 * q by omega]
    exact ZMod.natCast_self _
  have hrd : r + r = d := by
    change (q : ZMod (4 * q)) + (q : ZMod (4 * q)) = ((2 * q : ℕ) : ZMod (4 * q))
    rw [← Nat.cast_add, show q + q = 2 * q by omega]
  have hp : ∀ x, x + d ∈ P ↔ x ∈ P := by
    rw [hPeq]
    exact pair_periodic 1 d hdd
  have hqr : ∀ x, d - x ∈ Q ↔ x ∈ Q := by
    rw [hQeq, ← hrd]
    exact symmetric_triple r 1
  have hAeq : (fourA q).image (fun (a : ℕ) => (a : ZMod (4 * q))) = insert 0 (P ∪ Q) := by
    ext x
    simp only [fourA, P, Q, PN, QN, Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Nat.cast_zero]
    tauto
  have hBeq : (fourB q).image (fun (a : ℕ) => (a : ZMod (4 * q))) = insert d (P ∪ Q) := by
    ext x
    simp only [fourB, P, Q, PN, QN, d, Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto
  rw [hAeq, hBeq]
  exact homometric_of_periodic_reflected_components P Q d hdis hp hqr hzero hd

end OnePitchShift
