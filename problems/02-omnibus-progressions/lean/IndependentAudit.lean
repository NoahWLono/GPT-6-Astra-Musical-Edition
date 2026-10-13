import SharpBounds
import InfiniteRangeBound
import ExactImageCounts
namespace Omnibus
#print Chord
#print stacking
#print chord
#print step
#print OmnibusStep
#print sonority
#print ActualImage
#check nodes_exact
#check local_quotient_lift
#check universal_eight_type_bound
#check universal_infinite_seven_type_bound
#check eight_type_bound_is_attained
#check infinite_seven_type_bound_is_sharp
#check global_image_count_exact
#check global_approachable_count_exact
#print axioms nodes_exact
#print axioms local_quotient_lift
#print axioms universal_eight_type_bound
#print axioms universal_infinite_seven_type_bound
#print axioms eight_type_bound_is_attained
#print axioms infinite_seven_type_bound_is_sharp
#print axioms global_image_count_exact
#print axioms global_approachable_count_exact
-- These checks are review additions, not changes to the frozen proof roots.
theorem independent_fifty_five_types : nodes.length = 55 := by
  rw [nodes_exact]
  decide
-- Both sharp witnesses start at the same intrinsically valid, unapproachable chord.
theorem independent_finite_start_unapproachable : inImage (finiteWitness 0) = false := by decide
theorem independent_infinite_start_unapproachable : inImage (infiniteWitness 0) = false := by decide
#print axioms independent_fifty_five_types
#print axioms independent_finite_start_unapproachable
#print axioms independent_infinite_start_unapproachable
end Omnibus
