# Independent complete omnibus replay: PASS

Completed 2026-10-13. All 101 frozen author modules and the reviewer audit compiled freshly under Lean 4.32.2. An independently written finite reconstruction also passed. No original project object was reused, no process failed, and no resource cap was hit.

## Verified results

- Every finite admissible descending walk visits at most **8 distinct bass-relative upper-multiset types**, with an explicit eight-type finite witness.
- Every finite prefix of every infinite admissible descending walk visits at most **7 distinct types**, with an explicit genuinely infinite seven-type witness.
- The union of actual endpoints of the three descending moves from intrinsically valid ordered chords has cardinality **6840**.
- Its intersection with the valid ordered chords has cardinality **2232**.
- Additional reviewer Lean checks confirm **55 canonical nodes** and that **both sharp witnesses start at unapproachable chords**.

The six main bound/attainment/count exports report only `propext`, `Classical.choice`, and `Quot.sound`. All 434 printed axiom audits across 426 distinct declarations use subsets of those same standard axioms. No admitted proof, custom axiom, native-decision oracle, `extern`, or `implemented_by` occurs in the active frozen source text.

## Replay isolation and resources

The local closure was independently recomputed and matched the author's manifest: 101 modules, three roots, seven direct external import names. Sources were copied to a new directory; the output directory started absent and was created empty. The compiler's `LEAN_PATH` was that output directory plus the recorded Mathlib/package build directories. The author's project directory was absent, and no external search directory contained a colliding local module object. All frozen source hashes still match both the source snapshot and original files.

- 102 Lean compilations, including the reviewer audit; one compiler version check
- Compiler child CPU: **295.188491 seconds**
- Independent fixture CPU: **0.154832 seconds**
- Total actual child CPU: **295.343323 / 400 seconds**
- Maximum process CPU: **8.981411 seconds**
- Peak process RSS: **1,901,170,688 bytes**
- Enforced limits: 19.5-second CPU watchdog / 20-second hard CPU, 35-second wall, 2 GiB RSS, `-j1`, 64 MiB aggregate captured output, and 4 GiB free-disk floor

The exact Lean version/commit, binary checksum, Mathlib revision, package locks and actual package heads are recorded in `DEPENDENCY_LOCK.json`. This rebuild intentionally uses existing standard-library and Mathlib dependency objects; it does not claim a from-source compiler/dependency bootstrap.

## Independent reconstruction

A new Python checker recognized the chord predicate using all orderings of every four-note pitch-class multiset, compared it with an independent stacking-template construction, and then reconstructed all ordered states and moves. It loaded no Lean objects and imported none of the author's Python. It independently found 3240 valid ordered chords, 55 types, 49 directed edges, image counts 6840/2232, and all 55 frozen successor equations. The local quotient equality was checked from all 3240 actual representatives. Exhaustive node-plus-visited-set searches verified the finite and infinite 8/7 maxima even with repeated vertices. Both explicit witnesses and the full 36-state ordered period checked.

Those extra fixture counts are computational evidence, not automatically additional theorem exports. The independently added 55-node and unapproachable-start checks are separately compiled Lean theorems in `sources/IndependentAudit.lean`.

## Scope and source review

No circular premise, hidden graph assumption, or mismodeled count was found. `SEMANTIC_REVIEW.md` expands all predicates, count meanings, quantifiers, and proof bridges. In particular, 6840 counts possibly invalid endpoints, whereas 2232 adds endpoint validity; neither count is a type quotient or an edge count. The factor twelve preserves upper-voice order and is proved by a bijection. The source and move predicates match Definitions 4–6 of the supplied Pyle paper.

The 8/7 results use an explicit bass-relative upper-multiset convention and allow unapproachable initial chords. They do **not** resolve Pyle's Conjecture 1 or establish novelty. The lower modulo-three endpoint and separate cyclicity task are outside this frozen audit. Two stale historical source-comment phrases were preserved to honor the freeze; successful receipts determine current status.

## Evidence map

- `FROZEN_AUTHOR_MANIFEST.json`, `PREPARATION_AUDIT.json`: independent import/source checks
- `sources/`, `objects/`, `logs/`: preserved fresh inputs, outputs, and compiler logs
- `resource_receipt.json`, `fixture_resource_receipt.json`: per-process limits, CPU, RSS, hashes
- `AXIOM_AUDIT.json`, `logs/IndependentAudit.log`: exact exports, expanded predicates, axiom audits
- `independent_fixture_audit.py`, `independent_fixture_results.json`, `fixture.log`: independent reconstruction
- `SEMANTIC_REVIEW.md`: detailed semantic and circularity review
- `FINAL_AUDIT.json`, `SHA256SUMS`: machine-readable conclusion and evidence checksums

Compiler slot 2 has been released. No remote writes were performed.
