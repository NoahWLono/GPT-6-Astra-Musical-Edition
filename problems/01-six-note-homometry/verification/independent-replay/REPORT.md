# Independent frozen-source rebuild: six-note one-exchange existence

**Result: PASS.** All 33 frozen project modules and one independently written exact-statement fixture compiled successfully from a fresh object directory. No failure or resource-cap event occurred.

## What the theorem actually proves

For every positive integer n, there exist two six-element subsets A, B of Z/nZ with exactly five shared elements, identical directed-difference multiplicities, and no translation or reflection taking A to B, if and only if

> n ≥ 12 and (3 divides n or 4 divides n).

The declaration is `OnePitchShift.six_note_one_exchange_existence_iff`. Its only ambient hypothesis is `[NeZero n]`, equivalent to positivity for a natural number. There is no normalization assumption, no assumption that a witness comes from a displayed construction, and no presupposed homometry or inequivalence hypothesis.

The independent fixture `IndependentHomometryAudit.positive_modulus_exact_statement` restates the result with the explicit hypothesis `0 < n`, expands homometry into the integer sums of membership indicators, and expands dihedral equivalence into the two existential Finset-image equalities. It compiled against the freshly rebuilt theorem and contains no project-specific predicates in its statement.

For each displacement t, the sum over x in A of the indicator that x−t belongs to A counts exactly the ordered pairs (x,y) in A² satisfying x−y=t. Thus the formal homometry predicate is the ordinary directed-difference multiplicity definition. `DihedralEquivalent` explicitly includes every translation x↦x+t and every translated reflection x↦t−x.

## Mathematical scope review

- Arbitrary representatives with intersection five are normalized by a proved simultaneous-translation bridge, and the bridge proves the converse as well.
- Necessity first bounds the nonzero exchanged element's order to 2, 3, or 4, then proves the even-order divisibility refinement.
- The lower bound n≥12 is structural. The common set C, its reflected asymmetric component, and the two exchange endpoints occupy disjoint parts of the ambient group, yielding n≥|C|+ord(d)+2. Together with the order and divisibility restrictions, this excludes every smaller modulus. No exhaustive small-modulus enumeration is imported or used.
- Sufficiency uses fully symbolic families for n=4q, q≥3, and n=3q, q≥5. The only remaining 3-divisible endpoint, n=12, is already supplied by the 4q family. Their inequivalence proofs exclude all candidate translations and reflections symbolically; this is not an enumeration of moduli.

This verifies existence in the **one-exchange stratum**. It does not classify all six-note homometric pairs, produce an irredundant enumeration of this stratum, or formally verify the separate order-four quotient-count claim. Construction prior art and mathematical novelty are separate questions; this audit does not establish novelty.

## Independence and frozen evidence

The author explicitly froze the sources before copying. The copied manifest has SHA-256:

`30b6718a5a092793611c48c936b15d6812442b7dd0d85873a6c890b16b6d4636`

Main source `FullSixNoteExistence.lean`:

`fe4da08a9e86550f233b2df20670271071e0f51e972cb2f7e50643752e8cd213`

Independent exact-statement fixture:

`88caf5fe57131d077230774489c2da7b4382f52746acf5c41af759ca666bfa7c`

All original and copied source hashes still matched after compilation. The 33-module local topological order was derived independently from imports and then compared with the author's manifest. The recursive source import graph, including implicit Init, contains 2,593 modules including the fixture, with no unresolved import. Every source path, hash, and direct import list is recorded in `full_transitive_import_closure.json`.

The `objects` directory did not exist before this run. `LEAN_PATH` contained only that fresh directory and the pinned Mathlib/package object directories; the author's object directory was omitted. Standard-library and Mathlib/package objects were reused, not independently rebuilt. The trusted baseline is Lean 4.32.2 (commit f3b06c705e6c85f5314019d5d3baab0fec5b580c) and Mathlib commit 905b95818eb32af7874a58b427f50c1711a5e96c. Mathlib's tracked worktree was clean.

A comment-stripped scan of the local closure found no `sorry`, `admit`, custom `axiom`, `native_decide`, `implemented_by`, or `unsafe` token. More importantly, the fresh final-theorem and independent-fixture axiom audits each reported only:

- `propext`
- `Classical.choice`
- `Quot.sound`

## Resource receipts

Each compiler invocation used `-j1 -M1900`, a 19.5-second actual-CPU watchdog, a 20-second hard CPU limit, a 35-second wall watchdog, a 2 GiB RSS watchdog, a 64 MiB output/file-size ceiling, and a 4 GiB free-disk floor. The aggregate compiler allowance was 180 actual CPU seconds. The runner stops on the first failure or cap and preserves all evidence.

- Fresh Lean targets: 34, all passed; one additional bounded version check
- Actual compiler CPU, including version check: **100.326889 seconds**
- Separately recorded full source-closure scan CPU: **15.252878 seconds**
- Combined recorded compiler and source-scan CPU: **115.579767 seconds**
- Maximum compiler-process CPU: **14.974841 seconds**
- Maximum compiler-process wall time: **14.980499 seconds**
- Maximum compiler-process RSS: **1,915,617,280 bytes**, about 1.784 GiB
- Failures and resource-cap events: **zero**

Compiler CPU and peak RSS use per-process `wait4` resource results, supplemented by live process-tree monitoring. The compiler ledger does not pretend to measure incidental shell or report-generation overhead. `resource_receipt.json` preserves every command, exit status, source/object/log hash, and per-process measurement. The source-scan CPU is reported separately rather than silently omitted.

## Evidence index

- `verification.json`: concise machine-readable verdict and checks
- `resource_receipt.json`: actual compiler resource ledger and exact search path
- `source_closure.json`: independently derived local import graph and build order
- `full_transitive_import_closure.json`: complete recursively resolved source graph
- `author_frozen_sources.json`: unchanged author manifest
- `sources/IndependentExactStatement.lean`: expanded independently authored statement
- `logs/FullAudit.log`: exact theorem, definitions, and final axiom dependencies
- `logs/IndependentExactStatement.log`: exact expanded theorem and axiom dependencies
- `logs/ParametricAudit.log`: construction-family and normalized-theorem audits
- `EVIDENCE_SHA256SUMS`: integrity hashes for the principal evidence files

Historical author failures remain preserved in the author's original project; no failure log or prior source was erased by this audit.
