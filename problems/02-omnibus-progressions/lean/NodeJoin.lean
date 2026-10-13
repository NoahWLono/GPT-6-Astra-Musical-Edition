import SliceDefinitions
import NodeSlice0
import NodeSlice1
import NodeSlice2
import NodeSlice3
import NodeSlice4
import NodeSlice5
import NodeSlice6
import NodeSlice7
import NodeSlice8
import NodeSlice9
import NodeSlice10
import NodeSlice11
import CanonicalBridge

/-! Complete intrinsic node classification assembled from twelve slices. -/
namespace Omnibus

theorem node_partition : nodes = (List.range 12).flatMap nodeSlice := by
  unfold nodes candidates
  rw [List.filter_flatMap]
  rfl

def checkedNodeList : List Shape := [⟨0,3,6⟩,⟨0,3,7⟩,⟨0,3,8⟩,⟨0,3,9⟩,⟨0,4,7⟩,⟨0,4,8⟩,⟨0,4,9⟩,⟨0,5,8⟩,⟨0,5,9⟩,⟨0,6,9⟩,⟨1,4,8⟩,⟨1,5,8⟩,⟨1,5,9⟩,⟨2,5,8⟩,⟨2,5,9⟩,⟨2,6,9⟩,⟨3,3,6⟩,⟨3,3,7⟩,⟨3,3,8⟩,⟨3,3,9⟩,⟨3,4,8⟩,⟨3,5,8⟩,⟨3,5,9⟩,⟨3,6,6⟩,⟨3,6,8⟩,⟨3,6,9⟩,⟨3,6,10⟩,⟨3,7,7⟩,⟨3,7,8⟩,⟨3,7,9⟩,⟨3,7,10⟩,⟨3,7,11⟩,⟨3,8,8⟩,⟨3,9,9⟩,⟨4,4,7⟩,⟨4,4,8⟩,⟨4,4,9⟩,⟨4,5,8⟩,⟨4,5,9⟩,⟨4,6,9⟩,⟨4,7,7⟩,⟨4,7,8⟩,⟨4,7,9⟩,⟨4,7,10⟩,⟨4,7,11⟩,⟨4,8,8⟩,⟨4,8,9⟩,⟨4,8,11⟩,⟨4,9,9⟩,⟨5,5,8⟩,⟨5,5,9⟩,⟨5,8,8⟩,⟨5,9,9⟩,⟨6,6,9⟩,⟨6,9,9⟩]

theorem nodes_exact : nodes = checkedNodeList := by
  rw [node_partition]
  have hr : List.range 12 = [0,1,2,3,4,5,6,7,8,9,10,11] := by decide
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, node_slice_0, node_slice_1, node_slice_2, node_slice_3, node_slice_4, node_slice_5, node_slice_6, node_slice_7, node_slice_8, node_slice_9, node_slice_10, node_slice_11]
  rfl

theorem canonical_shape_bounds (c : Chord) :
    let q := sonority c
    q.x ≤ q.y ∧ q.y ≤ q.z ∧ q.z < 12 := by
  simp only [sonority, sort3]
  omega

theorem chord_type_in_nodes (c : Chord) (hc : chord c = true) :
    sonority c ∈ nodes := by
  have hb : bounded c = true := (Bool.and_eq_true_iff.mp hc).1
  have hch : chord (realize (sonority c)) = true := (canonical_chord c hb).trans hc
  obtain ⟨hxy,hyz,hz⟩ := canonical_shape_bounds c
  apply List.mem_filter.mpr
  refine ⟨?_,hch⟩
  simp only [candidates, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter]
  refine ⟨(sonority c).x, by omega, (sonority c).y, by omega,
    (sonority c).z, ⟨by omega, by simp [hxy,hyz]⟩, ?_⟩
  cases sonority c
  rfl

#print axioms nodes_exact
#print axioms chord_type_in_nodes
end Omnibus
