# 07. A variance bound for transverse rhythmic triplets and monochromatic queens

Author: **GPT-6 Astra**, the requested AI-project author label. This is an AI-generated research project, without any claim of official OpenAI affiliation or endorsement.

## Status and precise scope

A monochromatic nonattacking placement of t queens on a k-by-k board satisfies `t² - 1 <= 3k(k - t)`. The same bound holds for transverse triplets in an actual perfect rhythmic triplet tiling: a partition of 0,...,3k-1 into positive-gap three-term arithmetic progressions with pairwise distinct gaps.

The formalization proves the injective-array estimate, its bridge to the actual exact-cover tiling, and the one-color queens theorem. It includes t = 0. Subtraction occurs over the real numbers, not truncated natural subtraction.

This is a complete proof of a supporting obstruction. Existence of perfect rhythmic triplet tilings for all sufficiently large orders remains unresolved. Novelty is unestablished. The square-root and asymptotic forms in the paper are manuscript-level corollaries, not separately named Lean theorems.

## Read and verify

- [Paper](paper/transverse-bound.pdf) and [LaTeX source](paper/transverse-bound.tex)
- [Exact formal statements](STATEMENTS.md) and [source/prior-art limits](SOURCES_AND_LIMITS.md)
- [Rebuild instructions](REBUILD.md) and [frozen build manifest](build_manifest.json)
- [Independent audit](verification/INDEPENDENT_AUDIT.md), [independent receipt](verification/INDEPENDENT_RECEIPT.json), and [public-package replay](verification/PUBLIC_REPLAY.json)
- [Per-project checksums](SHA256SUMS)

The package contains five project modules plus one audit fixture. Its source-only replay uses fresh project objects; pinned compiler, standard-library, Mathlib and package caches are trusted dependencies rather than independently bootstrapped components.

The paper and Lean source bytes are retained from the completed research package. Any pre-release statement in a manuscript about publication status records the status at writing. This repository folder is the public source release; it does not represent a journal submission or an author response.
