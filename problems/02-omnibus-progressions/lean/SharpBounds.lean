import UniversalBounds
import PeriodicWitness
/-! Explicit sharpness assembly for the checked bounds. -/
namespace Omnibus

def finiteWitness (n : Nat) : Chord :=
  match n with
  | 0 => ⟨0,0,3,6⟩
  | 1 => ⟨11,0,3,7⟩
  | 2 => ⟨10,1,3,7⟩
  | 3 => ⟨9,1,4,7⟩
  | 4 => ⟨8,1,4,8⟩
  | 5 => ⟨7,1,4,9⟩
  | 6 => ⟨6,1,5,9⟩
  | _ => ⟨5,2,5,9⟩

theorem finite_witness_initial : chord (finiteWitness 0) = true := by decide

theorem finite_witness_steps : ∀ i : Fin 7,
    OmnibusStep (finiteWitness i.val) (finiteWitness (i.val+1)) := by
  unfold OmnibusStep
  decide

theorem finite_witness_eight_types :
    ((Finset.range 8).image (fun n => sonority (finiteWitness n))).card = 8 := by decide

theorem eight_type_bound_is_attained :
    ∃ c : Nat → Chord, chord (c 0) = true ∧
      (∀ k < 7, OmnibusStep (c k) (c (k+1))) ∧
      ((Finset.range 8).image (fun n => sonority (c n))).card = 8 := by
  exact ⟨finiteWitness, finite_witness_initial,
    (fun k hk => finite_witness_steps ⟨k,hk⟩), finite_witness_eight_types⟩

theorem periodic_edge (i : Fin 36) :
    OmnibusStep (periodicChord i) (periodicChord (cycleNext i)) := by
  exact ⟨(concrete_period_is_admissible i).1,
    (concrete_period_is_admissible (cycleNext i)).1,
    (concrete_period_is_admissible i).2⟩

theorem infinite_witness_is_admissible :
    ∀ n, OmnibusStep (infiniteWitness n) (infiniteWitness (n+1)) := by
  intro n
  cases n with
  | zero => unfold OmnibusStep; decide
  | succ n =>
    have hi : cycleNext ⟨n%36, Nat.mod_lt _ (by decide)⟩ =
        (⟨(n+1)%36, Nat.mod_lt _ (by decide)⟩ : Fin 36) := by
      apply Fin.ext
      simp only [cycleNext]
      omega
    have he := periodic_edge ⟨n%36,Nat.mod_lt _ (by decide)⟩
    rw [hi] at he
    simpa only [infiniteWitness, Nat.succ_ne_zero, if_false, Nat.succ_sub_one] using he

theorem infinite_witness_seven_types :
    ((Finset.range 7).image (fun n => sonority (infiniteWitness n))).card = 7 := by decide

theorem seven_prefix_bound_is_attained :
    ∃ c : Nat → Chord, (∀ n, OmnibusStep (c n) (c (n+1))) ∧
      ((Finset.range 7).image (fun n => sonority (c n))).card = 7 ∧
      sonority (c 7) = sonority (c 1) := by
  exact ⟨infiniteWitness, infinite_witness_is_admissible,
    infinite_witness_seven_types, first_repeat_is_second_type⟩

#print axioms eight_type_bound_is_attained
#print axioms infinite_witness_is_admissible
#print axioms seven_prefix_bound_is_attained
end Omnibus
