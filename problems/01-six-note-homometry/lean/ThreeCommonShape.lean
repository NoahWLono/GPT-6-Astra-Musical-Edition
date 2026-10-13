/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge
import CommonRepresentatives
import Mathlib.Tactic.Tauto

namespace OnePitchShift

theorem three_family_A_shape (q : ℕ) :
    (threeA q).image (fun (a : ℕ) => (a : ZMod (3 * q))) = insert 0 ((threeCommonNat q).image (fun (a : ℕ) => (a : ZMod (3 * q)))) := by
  ext x
  simp only [threeA, threeCommonNat, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton, Nat.cast_zero]

theorem three_family_B_shape (q : ℕ) :
    (threeB q).image (fun (a : ℕ) => (a : ZMod (3 * q))) = insert ((q : ℕ) : ZMod (3 * q)) ((threeCommonNat q).image (fun (a : ℕ) => (a : ZMod (3 * q)))) := by
  ext x
  simp only [threeB, threeCommonNat, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

end OnePitchShift
