/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import FourCommonCard
import FourCommonEndpoints
import FourCommonShape
import FourFamilyHomometry
import FourFamilyStrictness
import SixExchangeDefinition

namespace OnePitchShift

theorem four_family_six_exchange (q : ℕ) (hq : 3 ≤ q) : SixExchange (4 * q) := by
  refine ⟨((fourCommonNat q).image (fun (a : ℕ) => (a : ZMod (4 * q)))), ((2 * q : ℕ) : ZMod (4 * q)), four_common_card q hq,
    four_common_zero_not_mem q hq, four_common_exchange_not_mem q hq,
    four_exchange_ne_zero q hq, ?_, ?_⟩
  · rw [← four_family_A_shape, ← four_family_B_shape]
    exact four_family_homometric q hq
  · rw [← four_family_A_shape, ← four_family_B_shape]
    exact four_family_strict q hq

end OnePitchShift
