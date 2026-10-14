import ErdosDeepCounterexamples
namespace ErdosDeepTriples
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Concrete bridges: the chosen lists are genuine sets of stated cardinalities,
    all pair distances are positive and in the complete scanned range. -/
theorem audit_first_pair_count :
    (familyDistances 34 [1,6,12] [10,9,5]).length = 91 ∧
    (familyDistances 34 [1,6,12] [10,9,5]).all
      (fun d => 0 < d && d ≤ 34 / 2) = true := by decide
theorem audit_second_pair_count :
    (familyDistances 48 [1,6,18] [20,5,5]).length = 210 ∧
    (familyDistances 48 [1,6,18] [20,5,5]).all
      (fun d => 0 < d && d ≤ 48 / 2) = true := by decide
theorem audit_lengths :
    ([1,6,12].zip [10,9,5]).length = 3 ∧
    ([1,6,18].zip [20,5,5]).length = 3 ∧
    ([1,6,12].zip [10,9,5]).map (fun (g,k) => (apPoints 34 g k).length) = [10,9,5] ∧
    ([1,6,18].zip [20,5,5]).map (fun (g,k) => (apPoints 48 g k).length) = [20,5,5] := by decide
#print first_counterexample
#print second_counterexample
#print not_normalizedClassification
#print axioms audit_first_pair_count
#print axioms audit_second_pair_count
#print axioms audit_lengths
end ErdosDeepTriples
