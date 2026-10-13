/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import FamilyRepresentatives

namespace OnePitchShift

lemma four_translation_1 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, (q+1) + (1) ≠ b ∧ (q+1) + (1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_translation_2 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, (q) + (q-1) ≠ b ∧ (q) + (q-1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_translation_3 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, (q-1) + (q) ≠ b ∧ (q-1) + (q) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_translation_4 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, (1) + (q+1) ≠ b ∧ (1) + (q+1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_translation_5 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, (q-1) + (2*q) ≠ b ∧ (q-1) + (2*q) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_translation_6 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, (1) + (2*q+1) ≠ b ∧ (1) + (2*q+1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_reflection_1 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, 4 * q + (1) - (1) ≠ b ∧ 4 * q + (1) - (1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_reflection_2 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, 4 * q + (q-1) - (q-1) ≠ b ∧ 4 * q + (q-1) - (q-1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_reflection_3 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, 4 * q + (q) - (q) ≠ b ∧ 4 * q + (q) - (q) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_reflection_4 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, 4 * q + (q+1) - (q+1) ≠ b ∧ 4 * q + (q+1) - (q+1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_reflection_5 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, 4 * q + (2*q) - (1) ≠ b ∧ 4 * q + (2*q) - (1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

lemma four_reflection_6 (q : ℕ) (hq : 3 ≤ q) :
    ∀ b ∈ fourB q, 4 * q + (2*q+1) - (q-1) ≠ b ∧ 4 * q + (2*q+1) - (q-1) ≠ b + 4 * q := by
  intro b hb
  simp only [fourB, Finset.mem_insert, Finset.mem_singleton] at hb
  constructor <;> omega

end OnePitchShift
