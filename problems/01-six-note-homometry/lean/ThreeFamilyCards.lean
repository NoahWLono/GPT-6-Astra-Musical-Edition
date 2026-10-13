/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge

namespace OnePitchShift

theorem three_family_cards (q : ℕ) (hq : 5 ≤ q) :
    ((threeA q).image (fun (a : ℕ) => (a : ZMod (3 * q)))).card = 6 ∧
    ((threeB q).image (fun (a : ℕ) => (a : ZMod (3 * q)))).card = 6 := by
  have hA : ∀ a ∈ threeA q, a < 3 * q := by
    intro a ha
    simp only [threeA, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha | ha | ha | ha <;> omega
  have hB : ∀ b ∈ threeB q, b < 3 * q := by
    intro b hb
    simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb | hb | hb | hb | hb | hb <;> omega
  rw [cast_image_card _ _ hA, cast_image_card _ _ hB]
  constructor
  · unfold threeA
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    simp
  · unfold threeB
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    simp


end OnePitchShift
