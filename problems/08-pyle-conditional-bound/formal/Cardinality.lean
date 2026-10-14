import RawReading
import Mathlib.Data.Finset.Card

namespace Omnibus.RootMarked
/-- A genuine finite-set cardinality statement for the entire infinite range. -/
theorem full_range_cardinality (c : Nat → Chord) (h : Nat → HarmonicType)
 (hc : ∀ n, OmnibusStep (c n) (c (n+1)))
 (ha : ∃ p, OmnibusStep p (c 0))
 (hh : ∀ n, RawReads (c n) (h n)) :
 ∃ S : Finset HarmonicType,
   (∀ x, x ∈ S ↔ ∃ n, h n = x) ∧ 3 ≤ S.card ∧ S.card ≤ 6 := by
 classical
 obtain ⟨⟨h01,h02,h12⟩,L,hL,hcover⟩ := raw_three_to_six c h hc ha hh
 let S := L.toFinset.filter (fun x => ∃ n, h n = x)
 have hexact : ∀ x, x ∈ S ↔ ∃ n, h n = x := by
   intro x
   simp only [S, Finset.mem_filter, List.mem_toFinset]
   constructor
   · exact fun hp => hp.2
   · rintro ⟨n,rfl⟩
     exact ⟨hcover n, n, rfl⟩
 have hsub : {h 0,h 1,h 2} ⊆ S := by
   intro x hx
   simp only [Finset.mem_insert, Finset.mem_singleton] at hx
   rcases hx with rfl|rfl|rfl
   · exact (hexact _).mpr ⟨0,rfl⟩
   · exact (hexact _).mpr ⟨1,rfl⟩
   · exact (hexact _).mpr ⟨2,rfl⟩
 have hthree : ({h 0,h 1,h 2} : Finset HarmonicType).card = 3 := by
   simp [h01,h02,h12]
 refine ⟨S,hexact,?_,?_⟩
 · rw [← hthree]
   exact Finset.card_le_card hsub
 · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le L).trans hL)
#print axioms full_range_cardinality
end Omnibus.RootMarked
