import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace YustFolding

abbrev PitchSet := Finset ℤ
abbrev PC := Fin 12
abbrev PCSet := Finset PC

def pitchA : PitchSet := {0, 1, 2, 3, 6, 7, 9}
def pitchB : PitchSet := {0, 1, 2, 3, 6, 8, 9}
def pcA : PCSet := {0, 1, 3, 4, 6}
def pcB : PCSet := {0, 1, 3, 4, 7}

def invPitch (t : ℤ) (S : PitchSet) : PitchSet := S.image (fun x => t - x)
def invPC (t : PC) (S : PCSet) : PCSet := S.image (fun x => t - x)
def transPC (t : PC) (S : PCSet) : PCSet := S.image (fun x => t + x)

def pitchCore (S : PitchSet) (a b : ℤ) : PitchSet := (S.erase a).erase b
def pcCore (S : PCSet) (a b : PC) : PCSet := (S.erase a).erase b

def PCEquiv (S T : PCSet) : Prop :=
  ∃ t : PC, T = transPC t S ∨ T = invPC t S
instance (S T : PCSet) : Decidable (PCEquiv S T) := inferInstanceAs (Decidable (∃ _ : PC, _))

def PCFold (S T : PCSet) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ t : PC,
    invPC t (pcCore S a b) = pcCore S a b ∧
    PCEquiv (insert (t - a) (S.erase a)) T
instance (S T : PCSet) : Decidable (PCFold S T) := inferInstanceAs (Decidable (∃ a ∈ S, _))

-- Allowing any stabilizing transposition already includes every multiple of a
-- transposition in Definition 4: the stabilizer is a subgroup.
def PCShift (S T : PCSet) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ t : PC,
    transPC t (pcCore S a b) = pcCore S a b ∧
    PCEquiv (insert (t + a) (S.erase a)) T
instance (S T : PCSet) : Decidable (PCShift S T) := inferInstanceAs (Decidable (∃ a ∈ S, _))

-- Distinct subset types, stronger than two deletion occurrences of one type.
theorem pc_shared_subset_one : pcA.erase 6 = pcB.erase 7 := by decide

theorem pc_shared_subset_two :
    invPC 7 (pcA.erase 1) = pcB.erase 0 := by decide

theorem pc_shared_types_distinct :
    ¬ PCEquiv (pcA.erase 6) (pcA.erase 1) := by decide

theorem pc_not_fold : ¬ PCFold pcA pcB := by decide

theorem pc_not_shift : ¬ PCShift pcA pcB := by decide

theorem pc_not_equivalent : ¬ PCEquiv pcA pcB := by decide

def pitchIntervals (S : PitchSet) : Multiset ℕ :=
  ((S.product S).filter (fun p => p.1 < p.2)).val.map
    (fun p => (p.2 - p.1).natAbs)

def pcIntervals (S : PCSet) : Multiset ℕ :=
  ((S.product S).filter (fun p => p.1 < p.2)).val.map
    (fun p => min (p.2 - p.1).val (p.1 - p.2).val)

theorem pc_cardinalities : pcA.card = 5 ∧ pcB.card = 5 := by decide

theorem pc_shared_intervals :
    (pcIntervals pcA ∩ pcIntervals pcB).card = 9 := by decide

theorem pitch_shared_subset_one : pitchA.erase 7 = pitchB.erase 8 := by decide

theorem pitch_shared_subset_two :
    invPitch 9 (pitchA.erase 2) = pitchB.erase 1 := by decide

theorem pitch_cardinalities : pitchA.card = 7 ∧ pitchB.card = 7 := by decide

theorem pitch_shared_intervals :
    (pitchIntervals pitchA ∩ pitchIntervals pitchB).card = 20 := by decide

theorem pitch_interval_difference :
    pitchIntervals pitchA - pitchIntervals pitchB = {4} ∧
    pitchIntervals pitchB - pitchIntervals pitchA = {8} := by decide

-- This small finite check is only used after proving that every possible
-- (unbounded integer) axis lies between 0 and 18.
theorem pitch_no_core_bounded :
    ∀ t ∈ Finset.Icc (0 : ℤ) 18, ∀ S ∈ pitchA.powersetCard 5,
      invPitch t S ≠ S := by decide

theorem pitch_mem_bounds {x : ℤ} (hx : x ∈ pitchA) : 0 ≤ x ∧ x ≤ 9 := by
  simp only [pitchA, Finset.mem_insert, Finset.mem_singleton] at hx
  omega

theorem pitch_no_symmetric_five_subset (S : PitchSet)
    (hsub : S ⊆ pitchA) (hcard : S.card = 5) (t : ℤ) :
    invPitch t S ≠ S := by
  intro hsym
  have hne : S.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨x, hx⟩ := hne
  have hy : t - x ∈ S := by
    rw [← hsym]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hxB := pitch_mem_bounds (hsub hx)
  have hyB := pitch_mem_bounds (hsub hy)
  have ht : t ∈ Finset.Icc (0 : ℤ) 18 := by
    simp only [Finset.mem_Icc]
    omega
  exact pitch_no_core_bounded t ht S (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩) hsym

def PitchEquiv (S T : PitchSet) : Prop :=
  ∃ t : ℤ, T = S.image (fun x => t + x) ∨ T = invPitch t S

def PitchFold (S T : PitchSet) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ t : ℤ,
    invPitch t (pitchCore S a b) = pitchCore S a b ∧
    PitchEquiv (insert (t - a) (S.erase a)) T

theorem pitch_no_folding (T : PitchSet) : ¬ PitchFold pitchA T := by
  rintro ⟨a, ha, b, hb, hab, t, hsym, _⟩
  have hb' : b ∈ pitchA.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hc : (pitchCore pitchA a b).card = 5 := by
    unfold pitchCore
    rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
    decide
  exact pitch_no_symmetric_five_subset _
    (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)) hc t hsym

-- An explicit integer-axis bound discharges non-equivalence without bounding
-- the ambient pitch universe or silently replacing integers by a finite type.
theorem pitch_equiv_bounded {S T : PitchSet} (hsub : S ⊆ pitchA)
    (hzero : (0 : ℤ) ∈ T) (h : PitchEquiv S T) :
    ∃ t ∈ Finset.Icc (-9 : ℤ) 9,
      T = S.image (fun x => t + x) ∨ T = invPitch t S := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_, ht⟩
  rcases ht with ht | ht
  · have hzero' : (0 : ℤ) ∈ S.image (fun x => t + x) := ht ▸ hzero
    obtain ⟨x, hx, htx⟩ := Finset.mem_image.mp hzero'
    have hb := pitch_mem_bounds (hsub hx)
    simp only [Finset.mem_Icc]
    omega
  · have hzero' : (0 : ℤ) ∈ invPitch t S := ht ▸ hzero
    obtain ⟨x, hx, htx⟩ := Finset.mem_image.mp hzero'
    have hb := pitch_mem_bounds (hsub hx)
    simp only [Finset.mem_Icc]
    omega

theorem pitch_not_equivalent : ¬ PitchEquiv pitchA pitchB := by
  intro h
  have h' := pitch_equiv_bounded (Finset.Subset.refl _) (by decide) h
  have hn : ¬ (∃ t ∈ Finset.Icc (-9 : ℤ) 9,
      pitchB = pitchA.image (fun x => t + x) ∨ pitchB = invPitch t pitchA) := by decide
  exact hn h'

theorem pitch_shared_types_distinct :
    ¬ PitchEquiv (pitchA.erase 7) (pitchA.erase 2) := by
  intro h
  have h' := pitch_equiv_bounded (Finset.erase_subset _ _) (by decide) h
  have hn : ¬ (∃ t ∈ Finset.Icc (-9 : ℤ) 9,
      pitchA.erase 2 = (pitchA.erase 7).image (fun x => t + x) ∨
      pitchA.erase 2 = invPitch t (pitchA.erase 7)) := by decide
  exact hn h'

-- Two different deletions in each chord, with different T/I types. This
-- stronger version avoids any ambiguity about counting repeated subset types.
def TwoSharedDeletionTypes {α : Type*} [DecidableEq α]
    (E : Finset α → Finset α → Prop) (S T : Finset α) : Prop :=
  ∃ a₁ ∈ S, ∃ a₂ ∈ S, ∃ b₁ ∈ T, ∃ b₂ ∈ T,
    a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
    E (S.erase a₁) (T.erase b₁) ∧ E (S.erase a₂) (T.erase b₂) ∧
    ¬ E (S.erase a₁) (S.erase a₂)

theorem pc_shared_deletions : TwoSharedDeletionTypes PCEquiv pcA pcB := by
  refine ⟨6, by decide, 1, by decide, 7, by decide, 0, by decide,
    by decide, by decide, ?_, ?_, pc_shared_types_distinct⟩
  · exact ⟨0, Or.inl (by decide)⟩
  · exact ⟨7, Or.inr pc_shared_subset_two.symm⟩

theorem pitch_shared_deletions : TwoSharedDeletionTypes PitchEquiv pitchA pitchB := by
  refine ⟨7, by decide, 2, by decide, 8, by decide, 1, by decide,
    by decide, by decide, ?_, ?_, pitch_shared_types_distinct⟩
  · exact ⟨0, Or.inl (by decide)⟩
  · exact ⟨9, Or.inr pitch_shared_subset_two.symm⟩

-- Counterexample to the forward implication under stricter nondegeneracy and
-- exact-overlap hypotheses than the printed conjecture explicitly states.
theorem conjecture_one_counterexample :
    pitchA.card = 7 ∧ pitchB.card = 7 ∧ ¬ PitchEquiv pitchA pitchB ∧
    TwoSharedDeletionTypes PitchEquiv pitchA pitchB ∧
    (pitchIntervals pitchA ∩ pitchIntervals pitchB).card = Nat.choose 7 2 - 1 ∧
    ¬ PitchFold pitchA pitchB := by
  exact ⟨pitch_cardinalities.1, pitch_cardinalities.2, pitch_not_equivalent,
    pitch_shared_deletions, pitch_shared_intervals, pitch_no_folding pitchB⟩

theorem conjecture_two_counterexample :
    pcA.card = 5 ∧ pcB.card = 5 ∧ ¬ PCEquiv pcA pcB ∧
    TwoSharedDeletionTypes PCEquiv pcA pcB ∧
    (pcIntervals pcA ∩ pcIntervals pcB).card = Nat.choose 5 2 - 1 ∧
    ¬ (PCFold pcA pcB ∨ PCShift pcA pcB) := by
  exact ⟨pc_cardinalities.1, pc_cardinalities.2, pc_not_equivalent,
    pc_shared_deletions, pc_shared_intervals, not_or.mpr ⟨pc_not_fold, pc_not_shift⟩⟩

-- Source representatives: these finite statements include all transpositions
-- and inversions of the source, while PCFold/PCShift already allow every target
-- transposition and inversion.
theorem pc_no_operation_on_representatives : ∀ t : PC,
    ¬ PCFold (transPC t pcA) pcB ∧ ¬ PCFold (invPC t pcA) pcB ∧
    ¬ PCShift (transPC t pcA) pcB ∧ ¬ PCShift (invPC t pcA) pcB := by decide

theorem pc_no_operation_on_equivalent_source (S : PCSet) (h : PCEquiv pcA S) :
    ¬ (PCFold S pcB ∨ PCShift S pcB) := by
  obtain ⟨t, h | h⟩ := h
  · subst S
    exact not_or.mpr ⟨(pc_no_operation_on_representatives t).1,
      (pc_no_operation_on_representatives t).2.2.1⟩
  · subst S
    exact not_or.mpr ⟨(pc_no_operation_on_representatives t).2.1,
      (pc_no_operation_on_representatives t).2.2.2⟩

-- The literal multiple-of-x form of Definition 4 is included in PCShift.
theorem transPC_add (s t : PC) (S : PCSet) :
    transPC (s + t) S = transPC s (transPC t S) := by
  simp only [transPC, Finset.image_image, Function.comp_def, add_assoc]

def pcStabilizer (S : PCSet) : AddSubgroup PC where
  carrier := {t | transPC t S = S}
  zero_mem' := by
    change transPC 0 S = S
    ext x
    simp only [transPC, Finset.mem_image, zero_add, exists_eq_right]
  add_mem' := by
    intro s t hs ht
    change transPC (s + t) S = S
    rw [transPC_add, ht, hs]
  neg_mem' := by
    intro t ht
    change transPC (-t) S = S
    calc
      transPC (-t) S = transPC (-t) (transPC t S) := by rw [ht]
      _ = transPC (-t + t) S := (transPC_add _ _ _).symm
      _ = S := by simp [transPC]

theorem pc_stabilizer_integer_multiple (S : PCSet) (x : PC)
    (h : transPC x S = S) (k : ℤ) : transPC (k • x) S = S :=
  (pcStabilizer S).zsmul_mem h k

def PCShiftAsPrinted (S T : PCSet) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ x : PC,
    transPC x (pcCore S a b) = pcCore S a b ∧ ∃ k : ℤ,
    PCEquiv (insert (k • x + a) (S.erase a)) T

theorem printed_shift_is_shift (S T : PCSet) : PCShiftAsPrinted S T → PCShift S T := by
  rintro ⟨a, ha, b, hb, hab, x, hx, k, he⟩
  exact ⟨a, ha, b, hb, hab, k • x,
    pc_stabilizer_integer_multiple _ x hx k, he⟩

theorem pc_no_printed_shift_on_equivalent_source (S : PCSet) (h : PCEquiv pcA S) :
    ¬ PCShiftAsPrinted S pcB := by
  intro hs
  exact pc_no_operation_on_equivalent_source S h (Or.inr (printed_shift_is_shift _ _ hs))

-- No five-element symmetric core persists under any integer transposition or
-- inversion of pitchA. Pull the alleged core back by the inverse isometry.
def transPitch (t : ℤ) (S : PitchSet) : PitchSet := S.image (fun x => t + x)

theorem pitch_no_core_transposed (s : ℤ) (C : PitchSet)
    (hsub : C ⊆ transPitch s pitchA) (hcard : C.card = 5) (t : ℤ) :
    invPitch t C ≠ C := by
  intro hsym
  let D := transPitch (-s) C
  have hDsub : D ⊆ pitchA := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hsub hy)
    simpa using hz
  have hDcard : D.card = 5 := by
    change (C.image (fun x => -s + x)).card = 5
    rw [Finset.card_image_of_injective (f := fun x : ℤ => -s + x) C (by intro a b h; dsimp at h; omega)]
    exact hcard
  have hDsym : invPitch (t - 2 * s) D = D := by
    change invPitch (t - 2 * s) (transPitch (-s) C) = transPitch (-s) C
    calc
      _ = transPitch (-s) (invPitch t C) := by
        simp only [invPitch, transPitch, Finset.image_image, Function.comp_def]
        congr 1
        funext x
        ring
      _ = _ := by rw [hsym]
  exact pitch_no_symmetric_five_subset D hDsub hDcard _ hDsym

theorem pitch_no_core_inverted (s : ℤ) (C : PitchSet)
    (hsub : C ⊆ invPitch s pitchA) (hcard : C.card = 5) (t : ℤ) :
    invPitch t C ≠ C := by
  intro hsym
  let D := invPitch s C
  have hDsub : D ⊆ pitchA := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hsub hy)
    simpa using hz
  have hDcard : D.card = 5 := by
    change (C.image (fun x => s - x)).card = 5
    rw [Finset.card_image_of_injective (f := fun x : ℤ => s - x) C (by intro a b h; dsimp at h; omega)]
    exact hcard
  have hDsym : invPitch (2 * s - t) D = D := by
    change invPitch (2 * s - t) (invPitch s C) = invPitch s C
    calc
      _ = invPitch s (invPitch t C) := by
        simp only [invPitch, Finset.image_image, Function.comp_def]
        congr 1
        funext x
        ring
      _ = _ := by rw [hsym]
  exact pitch_no_symmetric_five_subset D hDsub hDcard _ hDsym

theorem pitch_no_folding_on_equivalent_source (S T : PitchSet)
    (heq : PitchEquiv pitchA S) : ¬ PitchFold S T := by
  have hScard : S.card = 7 := by
    obtain ⟨s, h | h⟩ := heq
    · rw [h, Finset.card_image_of_injective (f := fun x : ℤ => s + x) pitchA (by intro a b h; dsimp at h; omega)]
      exact pitch_cardinalities.1
    · rw [h]
      unfold invPitch
      rw [Finset.card_image_of_injective (f := fun x : ℤ => s - x) pitchA (by intro a b h; dsimp at h; omega)]
      exact pitch_cardinalities.1
  rintro ⟨a, ha, b, hb, hab, t, hsym, _⟩
  have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hCcard : (pitchCore S a b).card = 5 := by
    unfold pitchCore
    rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha, hScard]
  have hCsub : pitchCore S a b ⊆ S :=
    Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  obtain ⟨s, h | h⟩ := heq
  · exact pitch_no_core_transposed s _ (h ▸ hCsub) hCcard t hsym
  · exact pitch_no_core_inverted s _ (h ▸ hCsub) hCcard t hsym

theorem pitch_shared_subset_cardinalities :
    (pitchA.erase 7).card = 6 ∧ (pitchA.erase 2).card = 6 ∧
    (pitchB.erase 8).card = 6 ∧ (pitchB.erase 1).card = 6 := by decide

theorem pc_shared_subset_cardinalities :
    (pcA.erase 6).card = 4 ∧ (pcA.erase 1).card = 4 ∧
    (pcB.erase 7).card = 4 ∧ (pcB.erase 0).card = 4 := by decide

-- Formal statements use the stricter, unambiguous reading: n≥3, distinct
-- whole-set types, two distinct shared deletion types, exact interval overlap.
-- Allowing arbitrary source representatives and the literal printed T-shift
-- only strengthens the operation side of the conjecture.
def PitchConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ S T : PitchSet, S.card = n → T.card = n →
    ¬ PitchEquiv S T →
    ((TwoSharedDeletionTypes PitchEquiv S T ∧
      (pitchIntervals S ∩ pitchIntervals T).card = Nat.choose n 2 - 1) ↔
    (∃ S' : PitchSet, PitchEquiv S S' ∧ PitchFold S' T))

def PitchClassConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ S T : PCSet, S.card = n → T.card = n →
    ¬ PCEquiv S T →
    ((TwoSharedDeletionTypes PCEquiv S T ∧
      (pcIntervals S ∩ pcIntervals T).card = Nat.choose n 2 - 1) ↔
    (∃ S' : PCSet, PCEquiv S S' ∧ (PCFold S' T ∨ PCShiftAsPrinted S' T)))

theorem conjecture_one_false : ¬ PitchConjecture := by
  intro h
  obtain ⟨S, heq, hfold⟩ := (h 7 (by omega) pitchA pitchB
    pitch_cardinalities.1 pitch_cardinalities.2 pitch_not_equivalent).mp
      ⟨pitch_shared_deletions, pitch_shared_intervals⟩
  exact pitch_no_folding_on_equivalent_source S pitchB heq hfold

theorem conjecture_two_false : ¬ PitchClassConjecture := by
  intro h
  obtain ⟨S, heq, hop⟩ := (h 5 (by omega) pcA pcB
    pc_cardinalities.1 pc_cardinalities.2 pc_not_equivalent).mp
      ⟨pc_shared_deletions, pc_shared_intervals⟩
  rcases hop with hfold | hshift
  · exact pc_no_operation_on_equivalent_source S heq (Or.inl hfold)
  · exact pc_no_printed_shift_on_equivalent_source S heq hshift

#print axioms conjecture_one_false
#print axioms conjecture_two_false
#print axioms pc_no_operation_on_representatives
#print axioms pc_no_printed_shift_on_equivalent_source
#print axioms pitch_no_folding_on_equivalent_source
#print axioms conjecture_one_counterexample
#print axioms conjecture_two_counterexample
#print axioms pc_not_fold
#print axioms pc_not_shift
#print axioms pitch_no_folding

end YustFolding
