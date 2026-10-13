/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import ParametricFamilies
#print axioms OnePitchShift.homometric_of_periodic_reflected_components
#print axioms OnePitchShift.not_dihedral_of_nat_witnesses
#print axioms OnePitchShift.four_family_strict
#print axioms OnePitchShift.three_family_strict
#print axioms OnePitchShift.four_family_homometric
#print axioms OnePitchShift.three_family_homometric
#print axioms OnePitchShift.four_family_six_exchange
#print axioms OnePitchShift.three_family_six_exchange
#check @OnePitchShift.homometric_of_periodic_reflected_components
#check @OnePitchShift.four_family_strict
#check @OnePitchShift.three_family_strict
#check @OnePitchShift.four_family_homometric
#check @OnePitchShift.three_family_homometric
#check @OnePitchShift.four_family_six_exchange
#check @OnePitchShift.three_family_six_exchange
#print OnePitchShift.SixExchange
