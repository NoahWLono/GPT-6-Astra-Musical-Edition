/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import StrictnessCore

namespace OnePitchShift

lemma cast_mem_image_iff (n : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < n) (a : ℕ) (ha : a < n) :
    (a : ZMod n) ∈ S.image (fun (x : ℕ) => (x : ZMod n)) ↔ a ∈ S := by
  constructor
  · intro h
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
    have hh := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (hS b hb), ZMod.val_natCast_of_lt ha] at hh
    exact hh ▸ hb
  · intro h
    exact Finset.mem_image.mpr ⟨a, h, rfl⟩

lemma cast_image_card (n : ℕ) (S : Finset ℕ) (hS : ∀ x ∈ S, x < n) :
    (S.image (fun (x : ℕ) => (x : ZMod n))).card = S.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb heq
  have hh := congrArg ZMod.val heq
  rwa [ZMod.val_natCast_of_lt (hS a ha), ZMod.val_natCast_of_lt (hS b hb)] at hh

lemma cast_images_disjoint (n : ℕ) (P Q : Finset ℕ)
    (hP : ∀ x ∈ P, x < n) (hQ : ∀ x ∈ Q, x < n) (hdis : Disjoint P Q) :
    Disjoint (P.image (fun (x : ℕ) => (x : ZMod n))) (Q.image (fun (x : ℕ) => (x : ZMod n))) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.disjoint_left.mp hdis ha ((cast_mem_image_iff n Q hQ a (hP a ha)).mp hy)

end OnePitchShift
