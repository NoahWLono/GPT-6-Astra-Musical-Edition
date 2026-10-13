/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

namespace OnePitchShift

def fourA (q : ℕ) : Finset ℕ := {0, 1, q - 1, q, q + 1, 2 * q + 1}
def fourB (q : ℕ) : Finset ℕ := {1, q - 1, q, q + 1, 2 * q, 2 * q + 1}
def threeA (q : ℕ) : Finset ℕ := {0, 1, 2, q - 2, q + 1, 2 * q + 1}
def threeB (q : ℕ) : Finset ℕ := {1, 2, q - 2, q, q + 1, 2 * q + 1}

end OnePitchShift
