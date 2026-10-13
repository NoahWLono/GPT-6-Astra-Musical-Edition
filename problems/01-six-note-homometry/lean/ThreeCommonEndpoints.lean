/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge
import CommonRepresentatives

namespace OnePitchShift

theorem three_common_zero_not_mem (q : ℕ) (hq : 5 ≤ q) :
    (0 : ZMod (3 * q)) ∉ ((threeCommonNat q).image (fun (a : ℕ) => (a : ZMod (3 * q)))) := by
  have hz := cast_mem_image_iff (3 * q) (threeCommonNat q) (three_common_nat_bound q hq) 0 (by omega)
  rw [Nat.cast_zero] at hz
  rw [hz]
  simp only [threeCommonNat, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem three_common_exchange_not_mem (q : ℕ) (hq : 5 ≤ q) :
    ((q : ℕ) : ZMod (3 * q)) ∉ ((threeCommonNat q).image (fun (a : ℕ) => (a : ZMod (3 * q)))) := by
  rw [cast_mem_image_iff _ _ (three_common_nat_bound q hq) (q) (by omega)]
  simp only [threeCommonNat, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem three_exchange_ne_zero (q : ℕ) (hq : 5 ≤ q) : ((q : ℕ) : ZMod (3 * q)) ≠ 0 := by
  intro hh
  have hv := congrArg ZMod.val hh
  rw [ZMod.val_natCast_of_lt (show q < 3 * q by omega), ZMod.val_zero] at hv
  omega

end OnePitchShift
