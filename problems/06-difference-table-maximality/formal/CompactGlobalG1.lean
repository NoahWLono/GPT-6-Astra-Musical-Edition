import CompactMaximalityCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace DifferenceTableResearch.CompactMaximalG1
def piMap : Fin 10 → Fin 10 := ![9, 7, 5, 3, 0, 1, 6, 4, 8, 2]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 1 → QRow := ![![1, (1/20), (1/10), (3/10), (9/20), (3/20), (1/5), (1/4), (11/20)]]
def block : Fin 10 → Fin 9 := ![0, 1, 2, 3, 0, 4, 5, 6, 7, 8]
abbrev Choices := ∀ i : Fin 9, Equiv.Perm {a : Fin 10 // block a = i}
noncomputable def candidate (g : Choices) : Fin 10 ≃ Fin 10 := pi.trans (assembleFibers block g)
def map0 : Fin 10 → Fin 10 := ![9, 7, 5, 3, 0, 1, 6, 4, 8, 2]
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
  ![0, -1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]] }
def map1 : Fin 10 → Fin 10 := ![9, 7, 5, 3, 4, 1, 6, 0, 8, 2]
def cert1 : ReverseCertificate := {
  f := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  g := ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  weight := 1,
  zeroCoeff := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  recovery := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]] }
noncomputable def cert (g : Choices) : ReverseCertificate :=
  if (∀ e, candidate g e = map0 e) then cert0 else
  cert1
theorem valid : ∀ g : Choices, (cert g).Valid 0 1 pi (candidate g) := by decide +kernel
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) →
    ∀ z, TableHolds 0 1 σ z → TableHolds 0 1 pi z := by
  apply table_maximality_from_fibers 0 1 pi block
  · apply samples_bound_collisions 0 1 pi samples block
    · decide +kernel
    · decide +kernel
  · intro g; exact compact_reverse_sound 0 1 pi (candidate g) (cert g) (valid g)
#print axioms globally_maximal
end DifferenceTableResearch.CompactMaximalG1
