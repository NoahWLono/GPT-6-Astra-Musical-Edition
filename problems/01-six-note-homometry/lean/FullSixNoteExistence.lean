/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import SixNoteExistence
import Normalization

namespace OnePitchShift

theorem six_note_one_exchange_existence_iff (n : ℕ) [NeZero n] :
    (∃ A B : Finset (ZMod n), A.card = 6 ∧ B.card = 6 ∧ (A ∩ B).card = 5 ∧
      Homometric A B ∧ ¬ DihedralEquivalent A B) ↔
    12 ≤ n ∧ (3 ∣ n ∨ 4 ∣ n) := by
  exact (six_exchange_sets_iff_normalized n).trans (six_exchange_iff n)

end OnePitchShift
