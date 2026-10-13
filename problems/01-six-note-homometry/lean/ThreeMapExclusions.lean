/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import FamilyRepresentatives

namespace OnePitchShift

lemma three_translation_1 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, (q-2) + (1) ≠ b ∧ (q-2) + (1) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_translation_2 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, (q+1) + (2) ≠ b ∧ (q+1) + (2) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_translation_3 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, (1) + (q-2) ≠ b ∧ (1) + (q-2) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_translation_4 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, (2) + (q) ≠ b ∧ (2) + (q) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_translation_5 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, (1) + (q+1) ≠ b ∧ (1) + (q+1) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_translation_6 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, (1) + (2*q+1) ≠ b ∧ (1) + (2*q+1) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_reflection_1 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, 3 * q + (1) - (1) ≠ b ∧ 3 * q + (1) - (1) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_reflection_2 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, 3 * q + (2) - (2) ≠ b ∧ 3 * q + (2) - (2) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_reflection_3 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, 3 * q + (q-2) - (q-2) ≠ b ∧ 3 * q + (q-2) - (q-2) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_reflection_4 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, 3 * q + (q) - (1) ≠ b ∧ 3 * q + (q) - (1) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_reflection_5 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, 3 * q + (q+1) - (2) ≠ b ∧ 3 * q + (q+1) - (2) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma three_reflection_6 (q : ℕ) (hq : 5 ≤ q) :
    ∀ b ∈ threeB q, 3 * q + (2*q+1) - (1) ≠ b ∧ 3 * q + (2*q+1) - (1) ≠ b + 3 * q := by
  intro b hb
  simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

end OnePitchShift
