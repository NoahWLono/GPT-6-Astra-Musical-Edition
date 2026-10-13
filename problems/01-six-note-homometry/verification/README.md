# Verification evidence

`independent-replay/` contains the original independent replay's report,
source-freeze manifest, import graphs, resource receipts, compiler logs,
verification verdict, and audit scripts. Those files are preserved byte-for-
byte. They record an earlier successful replay of 33 frozen project modules
and one independent expanded-statement fixture.

Historical absolute paths identify the original cloud workspace. They are
not required installation paths. In those records, `sources/<module>.lean`
corresponds byte-for-byte to `../lean/<module>.lean` relative to this directory.
A duplicate of the small independent fixture is kept at the original evidence
path so that `EVIDENCE_SHA256SUMS` remains directly checkable. The remaining
source files are distributed once under `lean/`.

The original evidence hash index covers the principal files it lists; the
project-root `SHA256SUMS` covers the full distributable package. Object hashes
in the receipts identify historically produced fresh objects. No compiled
project object is distributed.

The import-closure scan resolved 2,593 source modules, including implicit Init,
with no unresolved imports. The scan does not imply that external libraries
were freshly rebuilt. The Lean compiler, standard library, and pinned
Mathlib/package objects remain the trusted baseline.

Use `../rebuild.py`, not the archived machine-specific audit scripts, for a
portable new replay. A preflight or static check is not a compiler replay.

## Public wrapper replay

`public-wrapper-replay/` preserves the subsequent end-to-end run of the exact
packaged wrapper. All 34 source compilations and all 13 expected named axiom
audits passed, reusing zero project objects. Actual aggregate compiler CPU was
86.060723 seconds, with no failure or resource cap. `PUBLIC_WRAPPER_REPLAY.json`
records the wrapper hash, environment-lock hash, and resource summary. No
compiled objects from that run are distributed.
