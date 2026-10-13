/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import FamilyRepresentatives

namespace OnePitchShift

def fourCommonNat (q : ℕ) : Finset ℕ := {1, q - 1, q, q + 1, 2 * q + 1}

lemma four_common_nat_bound (q : ℕ) (hq : 3 ≤ q) :
    ∀ a ∈ fourCommonNat q, a < 4 * q := by
  intro a ha
  simp only [fourCommonNat, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha | ha | ha | ha <;> omega

def threeCommonNat (q : ℕ) : Finset ℕ := {1, 2, q - 2, q + 1, 2 * q + 1}

lemma three_common_nat_bound (q : ℕ) (hq : 5 ≤ q) :
    ∀ a ∈ threeCommonNat q, a < 3 * q := by
  intro a ha
  simp only [threeCommonNat, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha | ha | ha | ha <;> omega

end OnePitchShift
