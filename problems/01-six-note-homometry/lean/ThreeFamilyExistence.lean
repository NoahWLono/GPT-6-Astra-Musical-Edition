/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ThreeCommonCard
import ThreeCommonEndpoints
import ThreeCommonShape
import ThreeFamilyHomometry
import ThreeFamilyStrictness
import SixExchangeDefinition

namespace OnePitchShift

theorem three_family_six_exchange (q : ℕ) (hq : 5 ≤ q) : SixExchange (3 * q) := by
  refine ⟨((threeCommonNat q).image (fun (a : ℕ) => (a : ZMod (3 * q)))), ((q : ℕ) : ZMod (3 * q)), three_common_card q hq,
    three_common_zero_not_mem q hq, three_common_exchange_not_mem q hq,
    three_exchange_ne_zero q hq, ?_, ?_⟩
  · rw [← three_family_A_shape, ← three_family_B_shape]
    exact three_family_homometric q hq
  · rw [← three_family_A_shape, ← three_family_B_shape]
    exact three_family_strict q hq

end OnePitchShift
