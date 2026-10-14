import SingletonGlobalMaximality
import DistinctMaximal22
import CompactGlobalG1
import CompactGlobalG2
import CompactGlobalB1
import CompactGlobalB2
import CompactGlobalB3
import CompactGlobalB6
import CompactGlobalC
import CompactGlobalG3
import CompactGlobalG4
import CompactGlobalB4
import CompactGlobalB5
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace DifferenceTableResearch.IndependentAudit
open DistinctMaximal22
theorem maps_bijective : ∀ i : Fin 22, Function.Bijective (maps i) := by decide +kernel
theorem all_nonempty : ∀ i : Fin 22, ∃ z, TableHolds (params i).1 (params i).2 (maps i) z := by
  have h : ∀ i : Fin 22, RationalTableHolds (params i).1 (params i).2 (maps i) (samples i 0) := by decide +kernel
  intro i
  exact ⟨fun j => (samples i 0 j : ℝ), rational_table_sound _ _ _ _ (h i)⟩
theorem all_maximal : ∀ (i : Fin 22) (σ : Fin 10 ≃ Fin 10),
    (∀ z, TableHolds (params i).1 (params i).2 (maps i) z → TableHolds (params i).1 (params i).2 σ z) →
    ∀ z, TableHolds (params i).1 (params i).2 σ z → TableHolds (params i).1 (params i).2 (maps i) z := by
  intro i σ inc z hz
  fin_cases i
  · have h := MaximalA1.globally_maximal σ inc
    change TableHolds 0 1 MaximalA1.pi z
    rw [h] at hz
    exact hz
  · have h := MaximalA2.globally_maximal σ inc
    change TableHolds 0 1 MaximalA2.pi z
    rw [h] at hz
    exact hz
  · have h := MaximalD1.globally_maximal σ inc
    change TableHolds 0 1 MaximalD1.pi z
    rw [h] at hz
    exact hz
  · have h := MaximalD2.globally_maximal σ inc
    change TableHolds 0 1 MaximalD2.pi z
    rw [h] at hz
    exact hz
  · have h := MaximalD3.globally_maximal σ inc
    change TableHolds 0 1 MaximalD3.pi z
    rw [h] at hz
    exact hz
  · have h := MaximalF1.globally_maximal σ inc
    change TableHolds 0 1 MaximalF1.pi z
    rw [h] at hz
    exact hz
  · have h := MaximalF2.globally_maximal σ inc
    change TableHolds 0 1 MaximalF2.pi z
    rw [h] at hz
    exact hz
  · exact CompactMaximalG1.globally_maximal σ inc z hz
  · exact CompactMaximalG2.globally_maximal σ inc z hz
  · exact CompactMaximalB1.globally_maximal σ inc z hz
  · have h := MaximalA3.globally_maximal σ inc
    change TableHolds 1 1 MaximalA3.pi z
    rw [h] at hz
    exact hz
  · exact CompactMaximalB2.globally_maximal σ inc z hz
  · exact CompactMaximalB3.globally_maximal σ inc z hz
  · exact CompactMaximalB6.globally_maximal σ inc z hz
  · have h := MaximalF3.globally_maximal σ inc
    change TableHolds 1 1 MaximalF3.pi z
    rw [h] at hz
    exact hz
  · exact CompactMaximalC.globally_maximal σ inc z hz
  · have h := MaximalD4.globally_maximal σ inc
    change TableHolds 1 2 MaximalD4.pi z
    rw [h] at hz
    exact hz
  · exact CompactMaximalG3.globally_maximal σ inc z hz
  · exact CompactMaximalG4.globally_maximal σ inc z hz
  · exact CompactMaximalB4.globally_maximal σ inc z hz
  · exact CompactMaximalB5.globally_maximal σ inc z hz
  · have h := MaximalF4.globally_maximal σ inc
    change TableHolds 2 2 MaximalF4.pi z
    rw [h] at hz
    exact hz
#check all_maximal
#print axioms all_maximal
#print axioms all_nonempty
#print axioms maps_bijective
#print axioms DistinctMaximal22.pairwise_distinct
end DifferenceTableResearch.IndependentAudit
