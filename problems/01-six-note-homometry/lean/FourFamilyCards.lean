/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import CastImageBridge

namespace OnePitchShift

theorem four_family_cards (q : ℕ) (hq : 3 ≤ q) :
    ((fourA q).image (fun (a : ℕ) => (a : ZMod (4 * q)))).card = 6 ∧
    ((fourB q).image (fun (a : ℕ) => (a : ZMod (4 * q)))).card = 6 := by
  have hA : ∀ a ∈ fourA q, a < 4 * q := by
    intro a ha
    simp only [fourA, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha | ha | ha | ha <;> omega
  have hB : ∀ b ∈ fourB q, b < 4 * q := by
    intro b hb
    simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb | hb | hb | hb | hb | hb <;> omega
  rw [cast_image_card _ _ hA, cast_image_card _ _ hB]
  constructor
  · unfold fourA
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    simp
  · unfold fourB
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)]
    simp


end OnePitchShift
