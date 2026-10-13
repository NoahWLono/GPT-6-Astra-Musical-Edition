/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ParametricFamilies
import SmallModuli

namespace OnePitchShift

theorem six_exchange_iff (n : ℕ) [NeZero n] :
    SixExchange n ↔ 12 ≤ n ∧ (3 ∣ n ∨ 4 ∣ n) := by
  constructor
  · intro h
    refine ⟨twelve_le_modulus_of_six_exchange n h, ?_⟩
    obtain ⟨C, d, hc, hz, hd, hne, hh, hs⟩ := h
    exact six_note_modulus_necessary n C d hz hd hne hc hh hs
  · rintro ⟨hn, hdiv⟩
    rcases hdiv with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · by_cases hq : 5 ≤ q
      · exact three_family_six_exchange q hq
      · have hq4 : q = 4 := by omega
        subst q
        exact four_family_six_exchange 3 (by decide)
    · exact four_family_six_exchange q (by omega)

end OnePitchShift
