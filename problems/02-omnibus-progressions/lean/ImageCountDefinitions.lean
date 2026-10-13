import NodeJoin
import CountTranslation
import Mathlib.Data.List.Dedup
/-! Canonical-source generation avoids re-running chord recognition.
The checkedNodeList equality is a checked theorem, not an assumed table. -/
namespace Omnibus

deriving instance ReflBEq, LawfulBEq for Chord

def upperOrderings (q : Shape) : List Chord :=
  [⟨0,q.x,q.y,q.z⟩,⟨0,q.x,q.z,q.y⟩,⟨0,q.y,q.x,q.z⟩,
   ⟨0,q.y,q.z,q.x⟩,⟨0,q.z,q.x,q.y⟩,⟨0,q.z,q.y,q.x⟩]

def sourceRaw : List Chord := checkedNodeList.flatMap upperOrderings

def normalizedMove (v : Fin 3) (c : Chord) : Chord := translate 1 (step v c)

def imageRaw : List Chord := sourceRaw.flatMap fun c => voices.map fun v => normalizedMove v c

def imageSlice (x : Nat) : List Chord :=
  ((imageRaw.filter fun c => c.tenor == x).dedup)

def approachableSlice (x : Nat) : List Chord :=
  (imageSlice x).filter fun c => sourceRaw.contains c

def sourceSlice (x : Nat) : List Chord :=
  ((sourceRaw.filter fun c => c.tenor == x).dedup)

end Omnibus
