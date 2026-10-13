import Pilot
namespace Omnibus
def closureCertificate (start : Shape) (C : List Shape) : Bool :=
  C.contains start &&
  C.all (fun p => (successors p).all (fun q => C.contains q)) &&
  decide ((C.filter (fun p => !(successors p).isEmpty)).length ≤ 7)

end Omnibus
