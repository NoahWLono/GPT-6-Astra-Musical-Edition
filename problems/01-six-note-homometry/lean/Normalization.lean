/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import SixExchangeDefinition
import TranslationBridge

namespace OnePitchShift

def SixExchangeSets (n : ℕ) : Prop :=
  ∃ A B : Finset (ZMod n), A.card = 6 ∧ B.card = 6 ∧ (A ∩ B).card = 5 ∧
    Homometric A B ∧ ¬ DihedralEquivalent A B

theorem six_exchange_sets_iff_normalized (n : ℕ) : SixExchangeSets n ↔ SixExchange n := by
  constructor
  · rintro ⟨A, B, hAc, hBc, hIc, hhom, hstrict⟩
    let C := A ∩ B
    have hCc : C.card = 5 := hIc
    obtain ⟨a, ha, hA⟩ := exists_insert_of_card_add_one C A
      Finset.inter_subset_left (by omega)
    obtain ⟨b, hb, hB⟩ := exists_insert_of_card_add_one C B
      Finset.inter_subset_right (by omega)
    have hba : b ≠ a := by
      intro h
      apply hb
      apply Finset.mem_inter.mpr
      constructor
      · rw [hA, h]
        exact Finset.mem_insert_self _ _
      · rw [hB]
        exact Finset.mem_insert_self _ _
    let C' := translated C (-a)
    let d := b - a
    have hzero : (0 : ZMod n) ∉ C' := by
      intro hz
      have hh : a + (-a) ∈ translated C (-a) := by simpa only [add_neg_cancel] using hz
      exact ha ((mem_translated C (-a) a).mp hh)
    have hd : d ∉ C' := by
      intro hz
      have hh : b + (-a) ∈ translated C (-a) := by
        simpa only [C', d, sub_eq_add_neg] using hz
      exact hb ((mem_translated C (-a) b).mp hh)
    have hdn : d ≠ 0 := by
      intro h
      exact hba (sub_eq_zero.mp h)
    have hAt : translated A (-a) = insert 0 C' := by
      rw [hA, translated_insert]
      simp only [add_neg_cancel, C']
    have hBt : translated B (-a) = insert d C' := by
      rw [hB, translated_insert]
      simp only [C', d, sub_eq_add_neg]
    refine ⟨C', d, ?_, hzero, hd, hdn, ?_, ?_⟩
    · rw [translated_card]
      exact hCc
    · rw [← hAt, ← hBt]
      exact homometric_translated A B (-a) hhom
    · rw [← hAt, ← hBt, dihedralEquivalent_translated_iff]
      exact hstrict
  · rintro ⟨C, d, hc, hzero, hd, hdne, hhom, hstrict⟩
    refine ⟨insert 0 C, insert d C, ?_, ?_, ?_, hhom, hstrict⟩
    · rw [Finset.card_insert_of_notMem hzero, hc]
    · rw [Finset.card_insert_of_notMem hd, hc]
    · have hi : insert 0 C ∩ insert d C = C := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hy⟩
          rcases hx with rfl | hx
          · rcases hy with h | hy
            · exact False.elim (hdne h.symm)
            · exact hy
          · exact hx
        · intro hx
          exact ⟨Or.inr hx, Or.inr hx⟩
      rw [hi, hc]

end OnePitchShift
