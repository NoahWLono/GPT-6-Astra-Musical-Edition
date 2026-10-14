# 06. Collision blocks and certified difference-table maximality

Author: **GPT-6 Astra**, the requested AI-project author label. This is an AI-generated research project, without any claim of official OpenAI affiliation or endorsement.

## Status and precise scope

For each of 22 explicit five-point difference-table loci, the package proves nonemptiness, bijectivity of the indexed edge map, pairwise distinction of the real solution loci, and maximality against every competing edge permutation in its fixed canonical chamber. The 22 representatives and their number are taken from Erickson–Jones. This is not a new classification.

A general collision criterion reduces possible dominators to permutations within sample collision blocks. There are 97 fiber-permutation choices across the 22 representatives, with at most 32 for one representative. The proof handles all 10! possible competitor permutations through this reduction.

The full intrinsic combinatorial characterization requested in Problem 5.1 remains unresolved here. No theorem proves completeness of the 22-element list, rules out an additional maximal locus, or derives an a priori selection rule. Literature-wide novelty is unestablished.

## Publication replay limitation

The original independent source rebuild **passed all 20 project modules**, followed by the independent aggregate and theorem/axiom export checks. Before this release, all 20 recorded source hashes and successful object hashes were rechecked, and every one of the 22 published Lean source hashes matched the frozen audit manifest.

The separate new public-wrapper replay is **incomplete because of a 6 GiB resident-memory cutoff**. It completed the first 14 modules, then was stopped during `CompactGlobalB6`; the remaining seven modules and fixtures were not attempted in that run. No Lean diagnostic error was emitted before termination. The release relies on the original completed independent source rebuild, not on a claimed full pass of this resource-limited replay. The exact source closure and portable wrapper are supplied for reproduction with sufficient memory.

## Read and verify

- [Paper](paper/difference-table-structural-partial.pdf) and [LaTeX source](paper/difference-table-structural-partial.tex)
- [Exact formal statements](STATEMENTS.md) and [source/prior-art limits](SOURCES_AND_LIMITS.md)
- [Rebuild instructions](REBUILD.md) and [frozen build manifest](build_manifest.json)
- [Independent audit](verification/INDEPENDENT_AUDIT.md), [independent receipt](verification/INDEPENDENT_RECEIPT.json), and [public-package replay](verification/PUBLIC_REPLAY.json)
- [Per-project checksums](SHA256SUMS)

The package contains 20 project modules plus two audit fixtures. The completed independent source rebuild used fresh project objects; pinned compiler, standard-library, Mathlib and package caches are trusted dependencies rather than independently bootstrapped components.

The paper and Lean source bytes are retained from the completed research package. Any pre-release statement in a manuscript about publication status records the status at writing. This repository folder is the public source release; it does not represent a journal submission or an author response.
