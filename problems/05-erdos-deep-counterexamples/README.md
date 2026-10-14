# Erdős-deep triple counterexamples

Author: GPT-6 Astra (project AI author label). Date: 14 October 2026.

The four-page paper is paper/erdos_deep_counterexamples.pdf; its editable LaTeX source is beside it. It gives full, elementary pair-count proofs for two counterexamples to the printed fifteen-triple necessity statement. The all-constituent strict-half-order variant is neither proved nor disproved. No absolute novelty or priority claim is made.

## Public rebuild

See [REBUILD.md](REBUILD.md) for the portable fresh-object check.

## Formal check

The development is ErdosDeepCounterexamples.lean, checked with Lean 4.32.2 and mathlib commit 905b95818eb32af7874a58b427f50c1711a5e96c. With that toolchain and mathlib already installed:

MATHLIB_DIR=/path/to/mathlib4 LEAN_BIN=/path/to/lean-4.32.2/bin ./check-lean.sh

The script compiles from source into a fresh temporary object; MATHLIB_DIR is required, and LEAN_BIN can be omitted when the pinned toolchain is already on PATH. The source prints its axiom audit, and verification-receipt.json records the results. No sorry, native_decide, or added axiom is used.

## Independent audit

independent-audit/ contains the external-to-discovery review report, independent point-set pair enumerator, frozen source, recorded environment versions and source hashes, and a separate Lean import harness. Read independent-audit/AUDIT.md for the exact scope.

The audited Lean source SHA-256 was 221f61a75a269f2dfe7c6e8a3f8f6977a87a9598b5be90705ff35cef98ea2805. The final source SHA-256 is d266bf8f3a11cb634b84d3fe63f90eb8e5958e3e0f38f3e83e444445dc15d918. The only difference is a corrected explanatory comment, from “stronger-than-literal” to “restricted-domain”; mathematical definitions and proofs are identical. Both files are included and the final file was rebuilt. Historical frozen prose was excluded from the deliverable to avoid propagating corrected source-citation errors. Its original hashes remain in source-sha256.txt with directory prefixes normalized to relative paths.

The audit's primary-source page extracts/screenshots are not redistributed here. Their original URLs, page numbers, hashes, and the audit findings are included; the PDF sources remain available from their publishers. No third-party source PDF is bundled.

## Other checks and rebuilds

- Run python search/verify.py to recheck all 649 supplied bounded-search hits by actual-point pair enumeration.
- Compile search/search.cpp with g++ -O3 -std=c++17, then run the binary with arguments 6 60 to regenerate the search CSV. This finite search is not a complete classification proof.
- Run python independent-audit/independent-count.py to repeat the independent two-example check and print its JSON results.
- Run ./build-paper.sh to rebuild the paper using a standard installed TeX Live setup.
- source-audit.md and prior-art-check.md document precise source scope and limited literature-search coverage.
- SHA256SUMS gives file-integrity checks. ./check-lean.sh and the Python checks remain the mathematical checks, not the hashes.


Raw compiler and console logs are omitted from the public package. The human audit reports, mathematical data, and JSON receipts retain the verified results. The source and independent audit harness reproduce the theorem and axiom checks.
