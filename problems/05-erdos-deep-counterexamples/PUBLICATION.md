# Publication package provenance

Prepared for the numbered public music repository on 14 October 2026.

The final Lean source, PDF, and LaTeX bytes match the completed source deliverable.
The Lean source SHA-256 is `d266bf8f3a11cb634b84d3fe63f90eb8e5958e3e0f38f3e83e444445dc15d918`.

Publication preparation changed documentation and build entry points only:
- Added a portable fresh-object wrapper, rebuild instructions, and local-output ignore rules.
- Replaced workspace-specific check entry points with calls to the portable wrapper.
- Updated README guidance and removed pre-publication status sentences.
- Added publication-wrapper JSON receipts and regenerated integrity manifests.
- Omitted all raw build, audit, search, and console logs, as well as PDF-info dumps.
- Removed machine-specific filesystem paths from build helpers and historical metadata.
- Simplified the paper helper to standard installed TeX commands; it was syntax-checked,
  while the previously rendered and inspected paper bytes remain unchanged.

The mathematical claims are bounded by the paper and independent audit. Neither
publication nor a successful build establishes novelty or priority. Historical
human audit reports and receipts remain separate from the publication-wrapper replay.
Compiled project objects, cache directories, search binaries, third-party source
PDFs, and unrelated research are not included.

The retained verification evidence consists of mathematical source files, human-readable audit conclusions, JSON receipts, explicit versions and source hashes, and independent mathematical data. The theorem and axiom output can be reproduced from the published sources. Raw log content is not embedded in these reports or any publication archive.
