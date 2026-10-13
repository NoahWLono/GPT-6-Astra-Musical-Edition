/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge
import CommonRepresentatives

namespace OnePitchShift

theorem four_common_zero_not_mem (q : ℕ) (hq : 3 ≤ q) :
    (0 : ZMod (4 * q)) ∉ ((fourCommonNat q).image (fun (a : ℕ) => (a : ZMod (4 * q)))) := by
  have hz := cast_mem_image_iff (4 * q) (fourCommonNat q) (four_common_nat_bound q hq) 0 (by omega)
  rw [Nat.cast_zero] at hz
  rw [hz]
  simp only [fourCommonNat, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem four_common_exchange_not_mem (q : ℕ) (hq : 3 ≤ q) :
    ((2 * q : ℕ) : ZMod (4 * q)) ∉ ((fourCommonNat q).image (fun (a : ℕ) => (a : ZMod (4 * q)))) := by
  rw [cast_mem_image_iff _ _ (four_common_nat_bound q hq) (2 * q) (by omega)]
  simp only [fourCommonNat, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem four_exchange_ne_zero (q : ℕ) (hq : 3 ≤ q) : ((2 * q : ℕ) : ZMod (4 * q)) ≠ 0 := by
  intro hh
  have hv := congrArg ZMod.val hh
  rw [ZMod.val_natCast_of_lt (show 2 * q < 4 * q by omega), ZMod.val_zero] at hv
  omega

end OnePitchShift
