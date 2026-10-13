import CountTranslation
import Mathlib.Logic.Equiv.Defs
/-! Guarded split of the capped bass-bijection draft. -/
namespace Omnibus
set_option maxHeartbeats 20000

abbrev PCTriple := Fin 12 × Fin 12 × Fin 12
abbrev PCChord := Fin 12 × PCTriple

def unpackChord (c : PCChord) : Chord :=
  ⟨c.1.val,c.2.1.val,c.2.2.1.val,c.2.2.2.val⟩
def unpackZero (t : PCTriple) : Chord := ⟨0,t.1.val,t.2.1.val,t.2.2.val⟩

def normalizePacked (c : PCChord) : PCChord :=
  (c.1, ⟨(c.2.1.val+12-c.1.val)%12,Nat.mod_lt _ (by decide)⟩,
    ⟨(c.2.2.1.val+12-c.1.val)%12,Nat.mod_lt _ (by decide)⟩,
    ⟨(c.2.2.2.val+12-c.1.val)%12,Nat.mod_lt _ (by decide)⟩)
def denormalizePacked (c : PCChord) : PCChord :=
  (c.1, ⟨(c.2.1.val+c.1.val)%12,Nat.mod_lt _ (by decide)⟩,
    ⟨(c.2.2.1.val+c.1.val)%12,Nat.mod_lt _ (by decide)⟩,
    ⟨(c.2.2.2.val+c.1.val)%12,Nat.mod_lt _ (by decide)⟩)

theorem packed_left_inverse (c : PCChord) : denormalizePacked (normalizePacked c) = c := by
  rcases c with ⟨⟨b,hb⟩,⟨t,ht⟩,⟨a,ha⟩,⟨s,hs⟩⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Fin.ext; dsimp [normalizePacked,denormalizePacked]; omega
    · apply Prod.ext
      · apply Fin.ext; dsimp [normalizePacked,denormalizePacked]; omega
      · apply Fin.ext; dsimp [normalizePacked,denormalizePacked]; omega

theorem packed_right_inverse (c : PCChord) : normalizePacked (denormalizePacked c) = c := by
  rcases c with ⟨⟨b,hb⟩,⟨t,ht⟩,⟨a,ha⟩,⟨s,hs⟩⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Fin.ext; dsimp [normalizePacked,denormalizePacked]; omega
    · apply Prod.ext
      · apply Fin.ext; dsimp [normalizePacked,denormalizePacked]; omega
      · apply Fin.ext; dsimp [normalizePacked,denormalizePacked]; omega

def bassNormalization : PCChord ≃ PCChord where
  toFun := normalizePacked
  invFun := denormalizePacked
  left_inv := packed_left_inverse
  right_inv := packed_right_inverse

theorem unpack_bounded (c : PCChord) : bounded (unpackChord c) = true := by
  simp [bounded,unpackChord]
theorem zero_bounded (c : PCTriple) : bounded (unpackZero c) = true := by
  simp [bounded,unpackZero]

theorem unpack_normalized (c : PCChord) :
    unpackZero (normalizePacked c).2 = translate (12-c.1.val) (unpackChord c) := by
  have hb := c.1.isLt
  dsimp [unpackZero,normalizePacked,translate,unpackChord]
  congr 1 <;> omega

theorem unpack_denormalized (b : Fin 12) (t : PCTriple) :
    unpackChord (denormalizePacked (b,t)) = translate b.val (unpackZero t) := by
  have hb := b.isLt
  dsimp [unpackChord,denormalizePacked,translate,unpackZero]
  congr 1 <;> omega


#print axioms bassNormalization
#print axioms unpack_normalized
#print axioms unpack_denormalized
end Omnibus
