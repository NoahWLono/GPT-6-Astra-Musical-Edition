# Verification evidence

`independent-replay/` preserves the independent replay's source provenance,
commands, resource receipts, logs, axiom outputs, and final audit. The original
JSON and log bytes have not been rewritten for publication.

The proof source set is provided once, in `../lean/`. Paths such as
`sources/IndependentGoldenFixture.lean` in the historical audit refer to
`../lean/IndependentGoldenFixture.lean` from this directory. All 20 source hashes
match their corresponding historical replay receipts. Historical `.olean`
files are deliberately excluded.

The manifest's `reference_olean_sha256` values refer to author objects from
before a comment-only cleanup. They are not replay evidence. The independent
replay ledger records the fresh objects actually checked after the source
freeze. The replay source hashes, not the earlier reference objects, are the
publication identity.

The resource figures describe the historical replay; they are measurements,
not guaranteed runtimes on other machines. Only standard Lean axioms occur in
the checked targets. The existing compiler and Mathlib/package objects remain
inside the documented trust boundary.

`public-wrapper-replay/` records the later successful compiler run using the
exact packaged `rebuild.py`. Its 20 source hashes match the same frozen closure.
`PUBLIC_WRAPPER_REPLAY_SUMMARY.json` binds the wrapper hash to this result and
records the measured CPU, wall, and sampled RSS figures. The earlier static
review and compiler-free preflight remain unchanged as historical stages;
their statements that no compiler was invoked apply to those stages only.
