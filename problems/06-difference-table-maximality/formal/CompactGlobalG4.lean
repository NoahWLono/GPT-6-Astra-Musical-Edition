import CompactMaximalityCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace DifferenceTableResearch.CompactMaximalG4
def piMap : Fin 10 → Fin 10 := ![4, 3, 6, 2, 8, 5, 1, 0, 9, 7]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 1 → QRow := ![![1, (1/10), (7/20), (2/5), (11/20), (1/4), (9/20), (11/20), (3/5)]]
def block : Fin 10 → Fin 9 := ![0, 1, 2, 3, 4, 5, 3, 6, 7, 8]
abbrev Choices := ∀ i : Fin 9, Equiv.Perm {a : Fin 10 // block a = i}
noncomputable def candidate (g : Choices) : Fin 10 ≃ Fin 10 := pi.trans (assembleFibers block g)
def map0 : Fin 10 → Fin 10 := ![4, 3, 6, 2, 8, 5, 1, 0, 9, 7]
def cert0 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]] }
def map1 : Fin 10 → Fin 10 := ![4, 6, 3, 2, 8, 5, 1, 0, 9, 7]
def cert1 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0],
  ![0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]] }
noncomputable def cert (g : Choices) : ReverseCertificate :=
  if (∀ e, candidate g e = map0 e) then cert0 else
  cert1
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
end DifferenceTableResearch.CompactMaximalG4
