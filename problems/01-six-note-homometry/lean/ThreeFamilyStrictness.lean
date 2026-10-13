/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ThreeMapExclusions

import StrictnessCore

namespace OnePitchShift

theorem three_family_strict (q : ℕ) (hq : 5 ≤ q) :
    ¬ DihedralEquivalent ((threeA q).image (fun (a : ℕ) => (a : ZMod (3 * q))))
      ((threeB q).image (fun (b : ℕ) => (b : ZMod (3 * q)))) := by
  apply not_dihedral_of_nat_witnesses
  · simp [threeA]
  · intro a ha
    simp only [threeA, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha | ha | ha | ha <;> omega
  · intro b hb
    simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb | hb | hb | hb | hb | hb <;> omega
  · intro t ht
    simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht | ht | ht | ht
    · subst t
      refine ⟨q-2, by simp [threeA], ?_⟩
      exact three_translation_1 q hq
    · subst t
      refine ⟨q+1, by simp [threeA], ?_⟩
      exact three_translation_2 q hq
    · subst t
      refine ⟨1, by simp [threeA], ?_⟩
      exact three_translation_3 q hq
    · subst t
      refine ⟨2, by simp [threeA], ?_⟩
      exact three_translation_4 q hq
    · subst t
      refine ⟨1, by simp [threeA], ?_⟩
      exact three_translation_5 q hq
    · subst t
      refine ⟨1, by simp [threeA], ?_⟩
      exact three_translation_6 q hq
  · intro t ht
    simp only [threeB, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht | ht | ht | ht
    · subst t
      refine ⟨1, by simp [threeA], ?_⟩
      exact three_reflection_1 q hq
    · subst t
      refine ⟨2, by simp [threeA], ?_⟩
      exact three_reflection_2 q hq
    · subst t
      refine ⟨q-2, by simp [threeA], ?_⟩
      exact three_reflection_3 q hq
    · subst t
      refine ⟨1, by simp [threeA], ?_⟩
      exact three_reflection_4 q hq
    · subst t
      refine ⟨2, by simp [threeA], ?_⟩
      exact three_reflection_5 q hq
    · subst t
      refine ⟨1, by simp [threeA], ?_⟩
      exact three_reflection_6 q hq

end OnePitchShift
