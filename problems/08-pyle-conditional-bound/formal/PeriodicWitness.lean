import Pilot
/-! concrete periodic infinite witness, no extension semantics. -/
namespace Omnibus

def periodStates : Array Chord := #[
  ⟨11,0,3,7⟩,
  ⟨10,1,3,7⟩,
  ⟨9,1,4,7⟩,
  ⟨8,1,4,8⟩,
  ⟨7,1,4,9⟩,
  ⟨6,1,5,9⟩,
  ⟨5,1,6,9⟩,
  ⟨4,1,7,9⟩,
  ⟨3,1,7,10⟩,
  ⟨2,2,7,10⟩,
  ⟨1,3,7,10⟩,
  ⟨0,3,7,11⟩,
  ⟨11,3,7,0⟩,
  ⟨10,3,7,1⟩,
  ⟨9,4,7,1⟩,
  ⟨8,4,8,1⟩,
  ⟨7,4,9,1⟩,
  ⟨6,5,9,1⟩,
  ⟨5,6,9,1⟩,
  ⟨4,7,9,1⟩,
  ⟨3,7,10,1⟩,
  ⟨2,7,10,2⟩,
  ⟨1,7,10,3⟩,
  ⟨0,7,11,3⟩,
  ⟨11,7,0,3⟩,
  ⟨10,7,1,3⟩,
  ⟨9,7,1,4⟩,
  ⟨8,8,1,4⟩,
  ⟨7,9,1,4⟩,
  ⟨6,9,1,5⟩,
  ⟨5,9,1,6⟩,
  ⟨4,9,1,7⟩,
  ⟨3,10,1,7⟩,
  ⟨2,10,2,7⟩,
  ⟨1,10,3,7⟩,
  ⟨0,11,3,7⟩
]

def periodicChord (i : Fin 36) : Chord := periodStates[i.val]'(by change i.val < 36; exact i.isLt)

def cycleNext (i : Fin 36) : Fin 36 := ⟨(i.val+1)%36,Nat.mod_lt _ (by decide)⟩

-- These finite assertions use the literal chord/move predicates.
theorem concrete_period_is_admissible : ∀ i : Fin 36,
    chord (periodicChord i) = true ∧
    ∃ v : Fin 3, step v (periodicChord i) = periodicChord (cycleNext i) := by decide

def infiniteWitness (n : Nat) : Chord :=
  if n = 0 then ⟨0,0,3,6⟩
  else periodicChord ⟨(n-1)%36,Nat.mod_lt _ (by decide)⟩

theorem first_seven_types_are_distinct :
    (((List.range 7).map infiniteWitness).map sonority).eraseDups.length = 7 := by decide

theorem first_repeat_is_second_type :
    sonority (infiniteWitness 7) = sonority (infiniteWitness 1) := by decide

-- The universal Nat-indexed path theorem is intentionally not assumed here.
-- It follows by n=0 / n=k+1 cases from concrete_period_is_admissible and
-- the equation cycleNext(k mod 36) = ((k+1) mod 36).
#print axioms concrete_period_is_admissible
#print axioms first_seven_types_are_distinct
#print axioms first_repeat_is_second_type
end Omnibus
