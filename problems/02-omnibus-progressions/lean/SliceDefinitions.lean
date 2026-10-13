import Pilot
namespace Omnibus
-- Each slice is calculated from intrinsic chord membership.
def candidateSlice (x : Nat) : List Shape :=
  (List.range 12).flatMap fun y =>
    ((List.range 12).filter fun z => x <= y && y <= z).map fun z => ⟨x,y,z⟩
def nodeSlice (x : Nat) : List Shape :=
  (candidateSlice x).filter fun q => chord (realize q)
end Omnibus
