import CompactMaximalityCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace DifferenceTableResearch.CompactMaximalC
def piMap : Fin 10 → Fin 10 := ![1, 2, 6, 3, 7, 0, 8, 5, 9, 4]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (2/9), (1/3), (7/18), (2/3), (1/3), (7/18), (5/9), (2/3)],
  ![1, (25/108), (1/3), (43/108), (2/3), (1/3), (43/108), (61/108), (2/3)]]
def block : Fin 10 → Fin 8 := ![0, 1, 2, 1, 3, 4, 5, 6, 1, 7]
abbrev Choices := ∀ i : Fin 8, Equiv.Perm {a : Fin 10 // block a = i}
noncomputable def candidate (g : Choices) : Fin 10 ≃ Fin 10 := pi.trans (assembleFibers block g)
def map0 : Fin 10 → Fin 10 := ![1, 2, 6, 3, 7, 0, 8, 5, 9, 4]
def cert0 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![-1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]] }
def map1 : Fin 10 → Fin 10 := ![1, 2, 6, 8, 7, 0, 3, 5, 9, 4]
def cert1 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }
def map2 : Fin 10 → Fin 10 := ![3, 2, 6, 1, 7, 0, 8, 5, 9, 4]
def cert2 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, -1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]] }
def map3 : Fin 10 → Fin 10 := ![3, 2, 6, 8, 7, 0, 1, 5, 9, 4]
def cert3 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]] }
def map4 : Fin 10 → Fin 10 := ![8, 2, 6, 1, 7, 0, 3, 5, 9, 4]
def cert4 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0]] }
def map5 : Fin 10 → Fin 10 := ![8, 2, 6, 3, 7, 0, 1, 5, 9, 4]
def cert5 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0]] }
noncomputable def cert (g : Choices) : ReverseCertificate :=
  if (∀ e, candidate g e = map0 e) then cert0 else
  if (∀ e, candidate g e = map1 e) then cert1 else
  if (∀ e, candidate g e = map2 e) then cert2 else
  if (∀ e, candidate g e = map3 e) then cert3 else
  if (∀ e, candidate g e = map4 e) then cert4 else
  cert5
theorem valid : ∀ g : Choices, (cert g).Valid 1 2 pi (candidate g) := by decide +kernel
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 1 2 pi z → TableHolds 1 2 σ z) →
    ∀ z, TableHolds 1 2 σ z → TableHolds 1 2 pi z := by
  apply table_maximality_from_fibers 1 2 pi block
  · apply samples_bound_collisions 1 2 pi samples block
    · decide +kernel
    · decide +kernel
  · intro g; exact compact_reverse_sound 1 2 pi (candidate g) (cert g) (valid g)
#print axioms globally_maximal
end DifferenceTableResearch.CompactMaximalC
