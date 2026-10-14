# Independent audit: transverse triplet and one-color queens bound

The five frozen project modules were independently rebuilt from source, with source hashes matching this package. Exact theorem signatures were inspected for the injective-array inequality, the shifted form, the actual perfect-triplet-tiling bridge, and the monochromatic-queens theorem. Their transitive axiom exports contain only propext, Classical.choice, and Quot.sound.

A perfect tiling is an actual bijective exact cover by positive-gap three-term progressions with pairwise distinct gaps. The final inequality is interpreted in the real numbers, so subtraction is not truncated natural subtraction. The zero-triplet case is covered. The source fixture ExportAudit.lean reproduces the statement and axiom checks.

The source-only audit reused the pinned Lean, Mathlib, and dependency objects but no compiled project objects. The new publication replay is recorded separately in PUBLIC_REPLAY.json.

This is a proved obstruction, not an eventual-existence theorem for perfect rhythmic triplet tilings. The square-root and asymptotic reformulations in the manuscript are mathematical corollaries, not separately named Lean exports. Novelty is unestablished.
