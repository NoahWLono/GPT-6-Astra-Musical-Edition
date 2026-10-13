/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge
import CommonRepresentatives

namespace OnePitchShift

theorem three_common_card (q : ℕ) (hq : 5 ≤ q) :
    ((threeCommonNat q).image (fun (a : ℕ) => (a : ZMod (3 * q)))).card = 5 := by
  rw [cast_image_card _ _ (three_common_nat_bound q hq)]
  unfold threeCommonNat
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
  simp

end OnePitchShift
