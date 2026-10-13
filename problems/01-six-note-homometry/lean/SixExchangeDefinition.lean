/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import EvenOrderRefinement
import Mathlib.Data.Fintype.Powerset

namespace OnePitchShift

/-- A normalized strict six-note one-exchange witness. -/
def SixExchange (n : ℕ) : Prop :=
  ∃ C : Finset (ZMod n), ∃ d : ZMod n,
    C.card = 5 ∧ 0 ∉ C ∧ d ∉ C ∧ d ≠ 0 ∧
    Homometric (insert 0 C) (insert d C) ∧
    ¬ DihedralEquivalent (insert 0 C) (insert d C)

instance (n : ℕ) [NeZero n] : Decidable (SixExchange n) := by
  unfold SixExchange Homometric DihedralEquivalent
  infer_instance

end OnePitchShift
