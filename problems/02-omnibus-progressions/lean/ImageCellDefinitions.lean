import ImageCountDefinitions
/-! Filter by both upper coordinates BEFORE duplicate removal. -/
namespace Omnibus

def imageCell (x y : Nat) : List Chord :=
  (imageRaw.filter fun c => c.tenor == x && c.alto == y).dedup

def approachableCell (x y : Nat) : List Chord :=
  (imageCell x y).filter fun c => sourceRaw.contains c
end Omnibus
