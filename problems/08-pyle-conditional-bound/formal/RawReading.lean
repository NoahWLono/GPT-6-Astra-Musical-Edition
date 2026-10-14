import RootMarkedBounds
namespace Omnibus.RootMarked
/-- Direct test on the four ordered voices' intervals above the bass. -/
def RawReads (c : Chord) (h : HarmonicType) : Prop :=
 h.inversion.val < (template h.quality).length ∧
 [0,(c.tenor+12-c.bass)%12,(c.alto+12-c.bass)%12,(c.soprano+12-c.bass)%12].all
   (relativeTemplate h).contains = true ∧
 (relativeTemplate h).all
   [0,(c.tenor+12-c.bass)%12,(c.alto+12-c.bass)%12,(c.soprano+12-c.bass)%12].contains = true

theorem reads_iff_raw (c : Chord) (h : HarmonicType) : Reads c h ↔ RawReads c h := by
 unfold Reads fits sonority RawReads
 rcases sort3_cases ((c.tenor+12-c.bass)%12) ((c.alto+12-c.bass)%12)
   ((c.soprano+12-c.bass)%12) with h0|h0|h0|h0|h0|h0 <;>
   rw [h0] <;>
   simp [List.all_eq_true, List.contains_iff_mem,
     and_assoc, and_left_comm, and_comm, or_assoc, or_left_comm, or_comm]


/-- The same theorem stated without a quotient in the root-reading premise. -/
theorem raw_three_to_six (c : Nat → Chord) (h : Nat → HarmonicType)
 (hc : ∀ n, OmnibusStep (c n) (c (n+1)))
 (ha : ∃ p, OmnibusStep p (c 0))
 (hh : ∀ n, RawReads (c n) (h n)) :
 (h 0 ≠ h 1 ∧ h 0 ≠ h 2 ∧ h 1 ≠ h 2) ∧
 ∃ L : List HarmonicType, L.length ≤ 6 ∧ ∀ n, h n ∈ L := by
 exact three_to_six c h hc ha (fun n => (reads_iff_raw _ _).mpr (hh n))
#print axioms raw_three_to_six
end Omnibus.RootMarked
