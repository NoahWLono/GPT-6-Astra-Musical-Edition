# Exact statements and limits

An infinite admissible walk of actual ordered four-voice pitch-class chords, using only the bass-down Definition 6 moves and whose initial chord has a valid admissible predecessor, has an entire quality/inversion range of cardinality between three and six under any valid root interpretation selected at each occurrence. Types forget common transposition and absolute roots but retain inversion relative to the selected root.

Both endpoints are attained. The witness supplement also exhibits a seven-type prefix of an infinite walk whose initial chord has no admissible predecessor, showing why that hypothesis matters.

This is a complete conditional theorem with explicit semantics. It does not identify those hypotheses with the intended but not fully formalized wording of Pyle's Conjecture 1, or define the original extension event. The source-interpretation question remains open in the paper's appendix. The package does not claim an unqualified solution of Conjecture 1. Novelty is unestablished. Mixed-direction walks are outside the theorem.

## Formal declarations

- `Omnibus.RootMarked.full_range_cardinality`: a finite set equal to the entire infinite type range, with cardinality between three and six
- `Omnibus.RootMarked.raw_three_to_six`: standard-library equivalent using attained distinct types and a covering list
- `formal/Witnesses.lean`: admissible periodic three- and six-type endpoint examples; a seven-type example with no admissible predecessor
- `formal/ExportAudit.lean` and `formal/WitnessExportAudit.lean`: exact statement and transitive-axiom checks

The theorem counts quality/inversion labels under a valid root reading, not literal voicings, occurrences, absolute roots, or an undefined extension event.
