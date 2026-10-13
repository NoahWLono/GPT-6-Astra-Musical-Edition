import SharpBounds
/-! Direct corollary of the already checked generic closed-set proof. -/
namespace Omnibus

theorem universal_infinite_seven_type_bound (c : Nat → Chord)
    (hc : ∀ k, OmnibusStep (c k) (c (k+1))) :
    ∀ N, ((Finset.range N).image (fun k => sonority (c k))).card ≤ 7 := by
  obtain ⟨C,h₀,hclosed,hcard⟩ := every_node_has_small_nonterminal_closure
    (sonority (c 0)) (chord_type_in_nodes (c 0) (hc 0).1)
  intro N
  exact ClosedWalkBounds.infinite_distinct_bound successors C hclosed hcard
    (fun k => sonority (c k)) h₀ (fun k => project_omnibus_step _ _ (hc k)) N

theorem infinite_seven_type_bound_is_sharp :
    ∃ c : Nat → Chord, (∀ k, OmnibusStep (c k) (c (k+1))) ∧
      (∀ N, ((Finset.range N).image (fun k => sonority (c k))).card ≤ 7) ∧
      ((Finset.range 7).image (fun k => sonority (c k))).card = 7 := by
  exact ⟨infiniteWitness,infinite_witness_is_admissible,
    universal_infinite_seven_type_bound infiniteWitness infinite_witness_is_admissible,
    infinite_witness_seven_types⟩

#print axioms universal_infinite_seven_type_bound
#print axioms infinite_seven_type_bound_is_sharp
end Omnibus
