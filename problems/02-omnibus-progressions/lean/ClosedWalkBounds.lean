import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
/-! Generic bounds from intrinsic closed-set certificates.
Requires the existing Mathlib 4.32.2 olean search paths in the future compiler gate.
No assumption in this generic module is a claimed fact about the omnibus graph. -/
namespace ClosedWalkBounds

variable {α : Type} [DecidableEq α] (succ : α → List α)

def Closed (C : List α) : Prop := ∀ a ∈ C, ∀ b ∈ succ a, b ∈ C
def nonterminal (C : List α) : List α := C.filter fun a => !(succ a).isEmpty

theorem stays_in_closed (C : List α) (hC : Closed succ C) (w : Nat → α)
    (h₀ : w 0 ∈ C) (n : Nat) (hw : ∀ k < n, w (k+1) ∈ succ (w k)) :
    ∀ k ≤ n, w k ∈ C := by
  intro k hk
  induction k with
  | zero => exact h₀
  | succ k ih => exact hC (w k) (ih (by omega)) (w (k+1)) (hw k (by omega))

theorem mem_nonterminal (C : List α) (a b : α) (ha : a ∈ C)
    (hab : b ∈ succ a) : a ∈ nonterminal succ C := by
  apply List.mem_filter.mpr
  exact ⟨ha, by simpa using (List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hab))⟩

/-- Counts all distinct visited vertices, even if the walk itself has repetitions. -/
theorem finite_distinct_bound (C : List α) (hC : Closed succ C)
    (hcard : (nonterminal succ C).length ≤ 7) (w : Nat → α)
    (h₀ : w 0 ∈ C) (n : Nat) (hw : ∀ k < n, w (k+1) ∈ succ (w k)) :
    ((Finset.range (n+1)).image w).card ≤ 8 := by
  have hmem := stays_in_closed succ C hC w h₀ n hw
  have hsub : (Finset.range (n+1)).image w ⊆
      insert (w n) (nonterminal succ C).toFinset := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
    have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
    by_cases hkn : k = n
    · subst k; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply List.mem_toFinset.mpr
      exact mem_nonterminal succ C (w k) (w (k+1)) (hmem k hk') (hw k (by omega))
  calc
    ((Finset.range (n+1)).image w).card ≤
        (insert (w n) (nonterminal succ C).toFinset).card := Finset.card_le_card hsub
    _ ≤ (nonterminal succ C).toFinset.card + 1 := Finset.card_insert_le _ _
    _ ≤ (nonterminal succ C).length + 1 := Nat.add_le_add_right (List.toFinset_card_le _) 1
    _ ≤ 8 := by omega

theorem infinite_distinct_bound (C : List α) (hC : Closed succ C)
    (hcard : (nonterminal succ C).length ≤ 7) (w : Nat → α)
    (h₀ : w 0 ∈ C) (hw : ∀ k, w (k+1) ∈ succ (w k)) (n : Nat) :
    ((Finset.range n).image w).card ≤ 7 := by
  have hmem : ∀ k, w k ∈ C := by
    intro k
    exact stays_in_closed succ C hC w h₀ k (fun i _ => hw i) k (Nat.le_refl k)
  have hsub : (Finset.range n).image w ⊆ (nonterminal succ C).toFinset := by
    intro a ha
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp ha
    exact List.mem_toFinset.mpr (mem_nonterminal succ C (w k) (w (k+1)) (hmem k) (hw k))
  exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans hcard)

theorem infinite_repeat_by_seven (C : List α) (hC : Closed succ C)
    (hcard : (nonterminal succ C).length ≤ 7) (w : Nat → α)
    (h₀ : w 0 ∈ C) (hw : ∀ k, w (k+1) ∈ succ (w k)) :
    ∃ i j : Nat, i < j ∧ j ≤ 7 ∧ w i = w j := by
  have hb := infinite_distinct_bound succ C hC hcard w h₀ hw 8
  have hlt : ((Finset.range 8).image w).card < (Finset.range 8).card := by
    simpa using Nat.lt_of_le_of_lt hb (by decide : 7 < 8)
  obtain ⟨i,hi,j,hj,hne,heq⟩ := Finset.exists_ne_map_eq_of_card_image_lt hlt
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  by_cases hij : i < j
  · exact ⟨i,j,hij,by omega,heq⟩
  · exact ⟨j,i,by omega,by omega,heq.symm⟩

#print axioms finite_distinct_bound
#print axioms infinite_distinct_bound
#print axioms infinite_repeat_by_seven
end ClosedWalkBounds
