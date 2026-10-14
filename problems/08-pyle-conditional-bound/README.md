# 08. A conditional root-marked three-to-six omnibus bound

Author: **GPT-6 Astra**, the requested AI-project author label. This is an AI-generated research project, without any claim of official OpenAI affiliation or endorsement.

## Status and precise scope

An infinite admissible walk of actual ordered four-voice pitch-class chords, using only the bass-down Definition 6 moves and whose initial chord has a valid admissible predecessor, has an entire quality/inversion range of cardinality between three and six under any valid root interpretation selected at each occurrence. Types forget common transposition and absolute roots but retain inversion relative to the selected root.

Both endpoints are attained. The witness supplement also exhibits a seven-type prefix of an infinite walk whose initial chord has no admissible predecessor, showing why that hypothesis matters.

This is a complete conditional theorem with explicit semantics. It does not identify those hypotheses with the intended but not fully formalized wording of Pyle's Conjecture 1, or define the original extension event. The source-interpretation question remains open in the paper's appendix. The package does not claim an unqualified solution of Conjecture 1. Novelty is unestablished. Mixed-direction walks are outside the theorem.

## Read and verify

- [Paper](paper/root_marked_omnibus.pdf) and [LaTeX source](paper/root_marked_omnibus.tex)
- [Exact formal statements](STATEMENTS.md) and [source/prior-art limits](SOURCES_AND_LIMITS.md)
- [Rebuild instructions](REBUILD.md) and [frozen build manifest](build_manifest.json)
- [Independent audit](verification/INDEPENDENT_AUDIT.md), [independent receipt](verification/INDEPENDENT_RECEIPT.json), and [public-package replay](verification/PUBLIC_REPLAY.json)
- [Per-project checksums](SHA256SUMS)

The package contains 28 project modules plus two audit fixtures. Its source-only replay uses fresh project objects; pinned compiler, standard-library, Mathlib and package caches are trusted dependencies rather than independently bootstrapped components.

The paper and Lean source bytes are retained from the completed research package. Any pre-release statement in a manuscript about publication status records the status at writing. This repository folder is the public source release; it does not represent a journal submission or an author response.
