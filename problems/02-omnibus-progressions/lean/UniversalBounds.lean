import NodeJoin
import LocalQuotientLift
import ClosureCertificates
import ClosedWalkBounds

/-! Concrete universal bounds with intrinsic semantic dependencies. -/
namespace Omnibus

theorem closure_certificate_semantics (q : Shape) (C : List Shape)
    (h : closureCertificate q C = true) :
    q ∈ C ∧ ClosedWalkBounds.Closed successors C ∧
      (ClosedWalkBounds.nonterminal successors C).length ≤ 7 := by
  simpa [closureCertificate, ClosedWalkBounds.Closed,
    ClosedWalkBounds.nonterminal, List.all_eq_true, and_assoc] using h

theorem every_node_has_small_nonterminal_closure (q : Shape) (hq : q ∈ nodes) :
    ∃ C : List Shape, q ∈ C ∧ ClosedWalkBounds.Closed successors C ∧
      (ClosedWalkBounds.nonterminal successors C).length ≤ 7 := by
  rw [nodes_exact] at hq
  simp only [checkedNodeList, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54
  · subst q
    exact ⟨closure_0, closure_certificate_semantics _ _ closure_certificate_0⟩
  · subst q
    exact ⟨closure_1, closure_certificate_semantics _ _ closure_certificate_1⟩
  · subst q
    exact ⟨closure_2, closure_certificate_semantics _ _ closure_certificate_2⟩
  · subst q
    exact ⟨closure_3, closure_certificate_semantics _ _ closure_certificate_3⟩
  · subst q
    exact ⟨closure_4, closure_certificate_semantics _ _ closure_certificate_4⟩
  · subst q
    exact ⟨closure_5, closure_certificate_semantics _ _ closure_certificate_5⟩
  · subst q
    exact ⟨closure_6, closure_certificate_semantics _ _ closure_certificate_6⟩
  · subst q
    exact ⟨closure_7, closure_certificate_semantics _ _ closure_certificate_7⟩
  · subst q
    exact ⟨closure_8, closure_certificate_semantics _ _ closure_certificate_8⟩
  · subst q
    exact ⟨closure_9, closure_certificate_semantics _ _ closure_certificate_9⟩
  · subst q
    exact ⟨closure_10, closure_certificate_semantics _ _ closure_certificate_10⟩
  · subst q
    exact ⟨closure_11, closure_certificate_semantics _ _ closure_certificate_11⟩
  · subst q
    exact ⟨closure_12, closure_certificate_semantics _ _ closure_certificate_12⟩
  · subst q
    exact ⟨closure_13, closure_certificate_semantics _ _ closure_certificate_13⟩
  · subst q
    exact ⟨closure_14, closure_certificate_semantics _ _ closure_certificate_14⟩
  · subst q
    exact ⟨closure_15, closure_certificate_semantics _ _ closure_certificate_15⟩
  · subst q
    exact ⟨closure_16, closure_certificate_semantics _ _ closure_certificate_16⟩
  · subst q
    exact ⟨closure_17, closure_certificate_semantics _ _ closure_certificate_17⟩
  · subst q
    exact ⟨closure_18, closure_certificate_semantics _ _ closure_certificate_18⟩
  · subst q
    exact ⟨closure_19, closure_certificate_semantics _ _ closure_certificate_19⟩
  · subst q
    exact ⟨closure_20, closure_certificate_semantics _ _ closure_certificate_20⟩
  · subst q
    exact ⟨closure_21, closure_certificate_semantics _ _ closure_certificate_21⟩
  · subst q
    exact ⟨closure_22, closure_certificate_semantics _ _ closure_certificate_22⟩
  · subst q
    exact ⟨closure_23, closure_certificate_semantics _ _ closure_certificate_23⟩
  · subst q
    exact ⟨closure_24, closure_certificate_semantics _ _ closure_certificate_24⟩
  · subst q
    exact ⟨closure_25, closure_certificate_semantics _ _ closure_certificate_25⟩
  · subst q
    exact ⟨closure_26, closure_certificate_semantics _ _ closure_certificate_26⟩
  · subst q
    exact ⟨closure_27, closure_certificate_semantics _ _ closure_certificate_27⟩
  · subst q
    exact ⟨closure_28, closure_certificate_semantics _ _ closure_certificate_28⟩
  · subst q
    exact ⟨closure_29, closure_certificate_semantics _ _ closure_certificate_29⟩
  · subst q
    exact ⟨closure_30, closure_certificate_semantics _ _ closure_certificate_30⟩
  · subst q
    exact ⟨closure_31, closure_certificate_semantics _ _ closure_certificate_31⟩
  · subst q
    exact ⟨closure_32, closure_certificate_semantics _ _ closure_certificate_32⟩
  · subst q
    exact ⟨closure_33, closure_certificate_semantics _ _ closure_certificate_33⟩
  · subst q
    exact ⟨closure_34, closure_certificate_semantics _ _ closure_certificate_34⟩
  · subst q
    exact ⟨closure_35, closure_certificate_semantics _ _ closure_certificate_35⟩
  · subst q
    exact ⟨closure_36, closure_certificate_semantics _ _ closure_certificate_36⟩
  · subst q
    exact ⟨closure_37, closure_certificate_semantics _ _ closure_certificate_37⟩
  · subst q
    exact ⟨closure_38, closure_certificate_semantics _ _ closure_certificate_38⟩
  · subst q
    exact ⟨closure_39, closure_certificate_semantics _ _ closure_certificate_39⟩
  · subst q
    exact ⟨closure_40, closure_certificate_semantics _ _ closure_certificate_40⟩
  · subst q
    exact ⟨closure_41, closure_certificate_semantics _ _ closure_certificate_41⟩
  · subst q
    exact ⟨closure_42, closure_certificate_semantics _ _ closure_certificate_42⟩
  · subst q
    exact ⟨closure_43, closure_certificate_semantics _ _ closure_certificate_43⟩
  · subst q
    exact ⟨closure_44, closure_certificate_semantics _ _ closure_certificate_44⟩
  · subst q
    exact ⟨closure_45, closure_certificate_semantics _ _ closure_certificate_45⟩
  · subst q
    exact ⟨closure_46, closure_certificate_semantics _ _ closure_certificate_46⟩
  · subst q
    exact ⟨closure_47, closure_certificate_semantics _ _ closure_certificate_47⟩
  · subst q
    exact ⟨closure_48, closure_certificate_semantics _ _ closure_certificate_48⟩
  · subst q
    exact ⟨closure_49, closure_certificate_semantics _ _ closure_certificate_49⟩
  · subst q
    exact ⟨closure_50, closure_certificate_semantics _ _ closure_certificate_50⟩
  · subst q
    exact ⟨closure_51, closure_certificate_semantics _ _ closure_certificate_51⟩
  · subst q
    exact ⟨closure_52, closure_certificate_semantics _ _ closure_certificate_52⟩
  · subst q
    exact ⟨closure_53, closure_certificate_semantics _ _ closure_certificate_53⟩
  · subst q
    exact ⟨closure_54, closure_certificate_semantics _ _ closure_certificate_54⟩

theorem project_omnibus_step (c d : Chord) (h : OmnibusStep c d) :
    sonority d ∈ successors (sonority c) := by
  exact (local_quotient_lift c h.1 (sonority d)).mpr ⟨d,h,rfl⟩

/-- Every finite admissible walk visits at most eight distinct bass-relative types. -/
theorem universal_eight_type_bound (c : Nat → Chord) (n : Nat)
    (hc₀ : chord (c 0) = true)
    (hc : ∀ k < n, OmnibusStep (c k) (c (k+1))) :
    ((Finset.range (n+1)).image (fun k => sonority (c k))).card ≤ 8 := by
  obtain ⟨C,h₀,hclosed,hcard⟩ := every_node_has_small_nonterminal_closure
    (sonority (c 0)) (chord_type_in_nodes (c 0) hc₀)
  exact ClosedWalkBounds.finite_distinct_bound successors C hclosed hcard
    (fun k => sonority (c k)) h₀ n (fun k hk => project_omnibus_step _ _ (hc k hk))

/-- Every infinite admissible walk repeats a type among its first eight positions. -/
theorem universal_seven_prefix_bound (c : Nat → Chord)
    (hc : ∀ k, OmnibusStep (c k) (c (k+1))) :
    ∃ i j : Nat, i < j ∧ j ≤ 7 ∧ sonority (c i) = sonority (c j) := by
  obtain ⟨C,h₀,hclosed,hcard⟩ := every_node_has_small_nonterminal_closure
    (sonority (c 0)) (chord_type_in_nodes (c 0) (hc 0).1)
  exact ClosedWalkBounds.infinite_repeat_by_seven successors C hclosed hcard
    (fun k => sonority (c k)) h₀ (fun k => project_omnibus_step _ _ (hc k))

#print axioms every_node_has_small_nonterminal_closure
#print axioms project_omnibus_step
#print axioms universal_eight_type_bound
#print axioms universal_seven_prefix_bound
end Omnibus
