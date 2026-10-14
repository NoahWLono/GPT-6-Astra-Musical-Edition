import RawReading
import PeriodicWitness
namespace Omnibus.RootMarked
def sixLabels : Array HarmonicType := #[
  ⟨6,3⟩,
  ⟨5,2⟩,
  ⟨5,0⟩,
  ⟨1,2⟩,
  ⟨5,3⟩,
  ⟨6,0⟩,
  ⟨6,3⟩,
  ⟨5,2⟩,
  ⟨5,0⟩,
  ⟨1,2⟩,
  ⟨5,3⟩,
  ⟨6,0⟩,
  ⟨6,3⟩,
  ⟨5,2⟩,
  ⟨5,0⟩,
  ⟨1,2⟩,
  ⟨5,3⟩,
  ⟨6,0⟩,
  ⟨6,3⟩,
  ⟨5,2⟩,
  ⟨5,0⟩,
  ⟨1,2⟩,
  ⟨5,3⟩,
  ⟨6,0⟩,
  ⟨6,3⟩,
  ⟨5,2⟩,
  ⟨5,0⟩,
  ⟨1,2⟩,
  ⟨5,3⟩,
  ⟨6,0⟩,
  ⟨6,3⟩,
  ⟨5,2⟩,
  ⟨5,0⟩,
  ⟨1,2⟩,
  ⟨5,3⟩,
  ⟨6,0⟩
]
def threeStates : Array Chord := #[
  ⟨0,0,4,8⟩,
  ⟨11,1,4,8⟩,
  ⟨10,1,5,8⟩,
  ⟨9,1,5,9⟩,
  ⟨8,1,5,10⟩,
  ⟨7,2,5,10⟩,
  ⟨6,2,6,10⟩,
  ⟨5,2,7,10⟩,
  ⟨4,2,7,11⟩,
  ⟨3,3,7,11⟩,
  ⟨2,4,7,11⟩,
  ⟨1,4,8,11⟩,
  ⟨0,4,8,0⟩,
  ⟨11,4,8,1⟩,
  ⟨10,5,8,1⟩,
  ⟨9,5,9,1⟩,
  ⟨8,5,10,1⟩,
  ⟨7,5,10,2⟩,
  ⟨6,6,10,2⟩,
  ⟨5,7,10,2⟩,
  ⟨4,7,11,2⟩,
  ⟨3,7,11,3⟩,
  ⟨2,7,11,4⟩,
  ⟨1,8,11,4⟩,
  ⟨0,8,0,4⟩,
  ⟨11,8,1,4⟩,
  ⟨10,8,1,5⟩,
  ⟨9,9,1,5⟩,
  ⟨8,10,1,5⟩,
  ⟨7,10,2,5⟩,
  ⟨6,10,2,6⟩,
  ⟨5,10,2,7⟩,
  ⟨4,11,2,7⟩,
  ⟨3,11,3,7⟩,
  ⟨2,11,4,7⟩,
  ⟨1,11,4,8⟩
]
def threeLabels : Array HarmonicType := #[
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩,
  ⟨3,0⟩,
  ⟨7,3⟩,
  ⟨7,0⟩
]
def sixH (i : Fin 36) : HarmonicType := sixLabels[i.val]'(by change i.val < 36; exact i.isLt)
def threeC (i : Fin 36) : Chord := threeStates[i.val]'(by change i.val < 36; exact i.isLt)
def threeH (i : Fin 36) : HarmonicType := threeLabels[i.val]'(by change i.val < 36; exact i.isLt)
def phase36 (n : Nat) : Fin 36 := ⟨n%36,Nat.mod_lt _ (by decide)⟩
theorem phase36_next (n : Nat) : cycleNext (phase36 n) = phase36 (n+1) := by
 apply Fin.ext
 simp only [cycleNext,phase36]
 omega

theorem six_finite_check : ∀ i : Fin 36,
 OmnibusStep (periodicChord i) (periodicChord (cycleNext i)) ∧ RawReads (periodicChord i) (sixH i) := by
 unfold OmnibusStep RawReads
 decide

theorem three_finite_check : ∀ i : Fin 36,
 OmnibusStep (threeC i) (threeC (cycleNext i)) ∧ RawReads (threeC i) (threeH i) := by
 unfold OmnibusStep RawReads
 decide

def sixChords (n : Nat) := periodicChord (phase36 n)
def sixHarmony (n : Nat) := sixH (phase36 n)
def threeChords (n : Nat) := threeC (phase36 n)
def threeHarmony (n : Nat) := threeH (phase36 n)

theorem six_steps : ∀ n, OmnibusStep (sixChords n) (sixChords (n+1)) := by
 intro n
 have hp := (six_finite_check (phase36 n)).1
 rw [phase36_next] at hp
 exact hp

theorem three_steps : ∀ n, OmnibusStep (threeChords n) (threeChords (n+1)) := by
 intro n
 have hp := (three_finite_check (phase36 n)).1
 rw [phase36_next] at hp
 exact hp

theorem six_approachable : ∃ p, OmnibusStep p (sixChords 0) := by
 refine ⟨periodicChord 35,?_⟩
 exact (six_finite_check 35).1

theorem three_approachable : ∃ p, OmnibusStep p (threeChords 0) := by
 refine ⟨threeC 35,?_⟩
 exact (three_finite_check 35).1

theorem six_readings : ∀ n, RawReads (sixChords n) (sixHarmony n) :=
 fun n => (six_finite_check (phase36 n)).2

theorem three_readings : ∀ n, RawReads (threeChords n) (threeHarmony n) :=
 fun n => (three_finite_check (phase36 n)).2

theorem six_attained : ((List.range 6).map sixHarmony).eraseDups.length = 6 := by decide

theorem three_range : ∀ n, threeHarmony n ∈ ([⟨3,0⟩,⟨7,3⟩,⟨7,0⟩] : List HarmonicType) := by
 have hp : ∀ i : Fin 36, threeH i ∈ ([⟨3,0⟩,⟨7,3⟩,⟨7,0⟩] : List HarmonicType) := by decide
 exact fun n => hp (phase36 n)

def sevenChords (n : Nat) := if n = 0 then (⟨0,0,3,6⟩ : Chord) else sixChords (n-1)
def sevenHarmony (n : Nat) := if n = 0 then (⟨2,0⟩ : HarmonicType) else sixHarmony (n-1)

theorem seven_steps : ∀ n, OmnibusStep (sevenChords n) (sevenChords (n+1)) := by
 intro n
 cases n with
 | zero => unfold OmnibusStep; decide
 | succ n => simpa [sevenChords] using six_steps n

theorem seven_readings : ∀ n, RawReads (sevenChords n) (sevenHarmony n) := by
 intro n
 cases n with
 | zero => unfold RawReads; decide
 | succ n => simpa [sevenChords,sevenHarmony] using six_readings n

theorem seven_attained : ((List.range 7).map sevenHarmony).eraseDups.length = 7 := by decide

theorem seven_not_approachable : ¬ ∃ p, OmnibusStep p (sevenChords 0) := by
 have hh : checkedNodeList.all (fun p => !(successors p).contains (sonority (sevenChords 0))) = true := by decide
 simp only [List.all_eq_true, Bool.not_eq_true',List.contains_iff_mem] at hh
 rintro ⟨p,hp⟩
 have hf := hh (sonority p) (nodes_exact ▸ chord_type_in_nodes p hp.1)
 have ht := List.contains_iff_mem.mpr (project hp)
 rw [hf] at ht
 contradiction
#print axioms six_steps
#print axioms three_steps
#print axioms six_attained
#print axioms seven_steps
#print axioms seven_not_approachable
end Omnibus.RootMarked
