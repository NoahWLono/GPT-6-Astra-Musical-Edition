# Verification evidence

## Independent complete replay: PASS

`independent-complete-replay/` archives the separate reviewer’s complete replay and independently written finite reconstruction. All 101 frozen author modules plus `IndependentAudit` compiled freshly. All 434 printed axiom audits over 426 distinct declarations used subsets of `propext`, `Classical.choice`, and `Quot.sound`.

- `FINAL_AUDIT.json`: final conclusion, exact counts, scope, resource totals
- `resource_receipt.json` and `logs/`: compiler receipts and output
- `fixture_resource_receipt.json`, `independent_fixture_audit.py`, `independent_fixture_results.json`, and `fixture.log`: independent reconstruction
- `AXIOM_AUDIT.json`: complete named axiom inventories
- `DEPENDENCY_LOCK.json`, `FROZEN_AUTHOR_MANIFEST.json`, `PREPARATION_AUDIT.json`: dependency and source identity
- `SEMANTIC_REVIEW.md`: expanded model, quantifiers, circularity check, source-paper match, and exclusions

The historical run used 295.343323 aggregate child CPU seconds, with peak RSS 1,901,170,688 bytes, zero failed processes, zero cap hits, and zero reused project objects. Existing Lean/Mathlib/package dependency objects were trusted.

Historical `sources/` correspond byte-for-byte to the package’s `lean/` files. Historical project objects are intentionally not distributed; receipts preserve their hashes. `SHA256SUMS.original-run.txt` is the complete original-run checksum record, not a checksum list intended to pass against this smaller archive. Use the package-root checksum files for distributed content.

## Portable public wrapper

`PUBLIC_WRAPPER_PREFLIGHT.json` records compiler-free pin/import checks. `PUBLIC_WRAPPER_STATIC_REVIEW.json` records nine noncompiler tests: terminal CPU, RSS, wall, output, and disk checks; an exit/kill race with truncated UTF-8; and parsing of all 426 expected audits. The wrapper was adapted from the previously tested sibling Golden package, adding the exact `Std` import/root, 102 frozen sources, all named audits, terminal kernel RSS accounting, and an aggregate generated-output check.

The separately authorized fresh public-wrapper retry **passed all 102 modules** in 264.240448 aggregate actual compiler CPU seconds. All 426 required distinct axiom audits matched, with 434 printed audit lines, zero failures/caps, and zero project-object reuse. `PUBLIC_WRAPPER_REPLAY.json` summarizes the result; `public-wrapper-replay/` preserves its terminal `RESULT.json`, complete ledger, preflight, receipts, and logs. This is a successful end-to-end run of the exact packaged wrapper, separate from compiler-free checks.

`public-wrapper-interrupted/` preserves the first attempt, interrupted when the execution transport disconnected. Its 71 completed modules passed without a recorded cap, using 175.692851 recorded actual CPU seconds. `ImageCellBlock6_1` has an empty log and no terminal receipt; its actual CPU is unknown, with a 20-second hard process limit. This interrupted attempt is not a complete pass and its objects are never reused by the fresh retry. `INTERRUPTED.json` states the limitation explicitly.

The portable Python adapter was separately replayed successfully and reproduced the exact original fixture result; see `PUBLIC_FIXTURE_REPLAY.json`. This is computational evidence separate from the Lean replay budget.

## Manuscript and package

`paper-qa/` records the final two-pass PDFLaTeX build, PDF metadata, and mechanical transcription checks. The authoring worker visually inspected every page. The subsequent user-requested GPT-6 Astra author-label edition was rebuilt in two PDFLaTeX passes and all eight pages were visually inspected again. Pages 2–8 are pixel-identical to the preceding edition. The attribution edit did not change any Lean, wrapper, lock, or replay bytes. Its theorem map was adapted only for package-relative paths. The historical paper checksum record is distinguished from the current `paper/SHA256SUMS`.

`PACKAGING_PREFLIGHT.json` checks source identity, source count, prohibited active proof tokens, portable script syntax, and absence of distributed project objects. `author-development/` preserves selected historical gate reports and honest log/receipt evidence, including failed attempts. Historical experimental proof-source snapshots are kept privately and are not distributed. The public package contains only the 102 successfully checked Lean inputs; historical receipts do not promise bundled experimental sources.

Scope remains: literal endpoint counts 6840/2232; sharp descending finite 8 / infinite all-prefix 7 bounds under the stated quotient; unapproachable witness starts; no solution/disproof of Conjecture 1; no established priority.
