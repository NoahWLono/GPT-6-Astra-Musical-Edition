import BassNatCardinality
/-! Encoded Fin-12 quadruples count actual bounded ordered chords. -/
namespace Omnibus
set_option maxHeartbeats 20000

def packChord (c : Chord) (hc : bounded c = true) : PCChord :=
  let h := bounded_fields c hc
  (⟨c.bass,h.1⟩,⟨c.tenor,h.2.1⟩,⟨c.alto,h.2.2.1⟩,⟨c.soprano,h.2.2.2⟩)

theorem unpack_packChord (c : Chord) (hc : bounded c = true) :
    unpackChord (packChord c hc) = c := by cases c; rfl

def actualChordPredicateEquiv (P : Chord → Prop) :
    {c : PCChord // P (unpackChord c)} ≃ {c : Chord // bounded c = true ∧ P c} where
  toFun c := ⟨unpackChord c.val,unpack_bounded c.val,c.property⟩
  invFun c := ⟨packChord c.val c.property.1, by
    rw [unpack_packChord]; exact c.property.2⟩
  left_inv c := by
    apply Subtype.ext
    rcases c with ⟨⟨b,t,a,s⟩,hc⟩
    rfl
  right_inv c := by
    apply Subtype.ext
    exact unpack_packChord c.val c.property.1

def ActualImage (c : Chord) : Prop :=
  ∃ d : Chord, chord d = true ∧ ∃ v : Fin 3, step v d = c

theorem actualImage_iff (c : Chord) :
    ActualImage c ↔ bounded c = true ∧ inImage c = true := by
  constructor
  · rintro ⟨d,hd,v,rfl⟩
    have hb := step_bounded v d
    exact ⟨hb,(image_membership _ hb).mpr ⟨d,hd,v,rfl⟩⟩
  · rintro ⟨hb,hi⟩
    exact (image_membership c hb).mp hi

def actualImageEquiv :
    {c : Chord // bounded c = true ∧ inImage c = true} ≃
      {c : Chord // ActualImage c} where
  toFun c := ⟨c.val,(actualImage_iff c.val).mpr c.property⟩
  invFun c := ⟨c.val,(actualImage_iff c.val).mp c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def actualApproachableEquiv :
    {c : Chord // bounded c = true ∧ chord c = true ∧ inImage c = true} ≃
      {c : Chord // chord c = true ∧ ActualImage c} where
  toFun c := ⟨c.val,c.property.2.1,
    (actualImage_iff c.val).mpr ⟨c.property.1,c.property.2.2⟩⟩
  invFun c := ⟨c.val,chord_is_bounded c.val c.property.1,c.property.1,
    ((actualImage_iff c.val).mp c.property.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_image_cardinality_eq_packed :
    Nat.card {c : Chord // ActualImage c} =
      Nat.card {c : PCChord // inImage (unpackChord c) = true} := by
  exact (Nat.card_congr ((actualChordPredicateEquiv (fun c => inImage c = true)).trans
    actualImageEquiv)).symm

theorem actual_approachable_cardinality_eq_packed :
    Nat.card {c : Chord // chord c = true ∧ ActualImage c} =
      Nat.card {c : PCChord // chord (unpackChord c) = true ∧ inImage (unpackChord c) = true} := by
  exact (Nat.card_congr ((actualChordPredicateEquiv
    (fun c => chord c = true ∧ inImage c = true)).trans actualApproachableEquiv)).symm

#print axioms actualChordPredicateEquiv
#print axioms actual_image_cardinality_eq_packed
#print axioms actual_approachable_cardinality_eq_packed
end Omnibus
