/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import FullSixNoteExistence
#print axioms OnePitchShift.strict_exchange_ambient_bound
#print axioms OnePitchShift.twelve_le_modulus_of_six_exchange
#print axioms OnePitchShift.six_exchange_sets_iff_normalized
#print axioms OnePitchShift.six_note_one_exchange_existence_iff
#check @OnePitchShift.six_exchange_sets_iff_normalized
#check @OnePitchShift.six_note_one_exchange_existence_iff
#print OnePitchShift.Homometric
#print OnePitchShift.autocorrelation
#print OnePitchShift.DihedralEquivalent
