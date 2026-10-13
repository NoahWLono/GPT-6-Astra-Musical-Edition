/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge
import CommonRepresentatives
import Mathlib.Tactic.Tauto

namespace OnePitchShift

theorem four_family_A_shape (q : ℕ) :
    (fourA q).image (fun (a : ℕ) => (a : ZMod (4 * q))) = insert 0 ((fourCommonNat q).image (fun (a : ℕ) => (a : ZMod (4 * q)))) := by
  ext x
  simp only [fourA, fourCommonNat, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton, Nat.cast_zero]

theorem four_family_B_shape (q : ℕ) :
    (fourB q).image (fun (a : ℕ) => (a : ZMod (4 * q))) = insert ((2 * q : ℕ) : ZMod (4 * q)) ((fourCommonNat q).image (fun (a : ℕ) => (a : ZMod (4 * q)))) := by
  ext x
  simp only [fourB, fourCommonNat, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

end OnePitchShift
