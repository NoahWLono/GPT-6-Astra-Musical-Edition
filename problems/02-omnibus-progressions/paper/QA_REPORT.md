# Final paper QA

Status: PASS. Finalized 13 October 2026.

## Deliverables

- `omnibus_bounds.tex`: editable LaTeX manuscript
- `omnibus_bounds.pdf`: eight-page, US Letter PDF
- `THEOREM_SOURCE_MAP.md`: exact claim-to-proof/evidence map and bibliographic checks
- `build.sh`: local two-pass pdfLaTeX build and render script
- `SHA256SUMS`: checksums of final paper files

## Mathematical and scope checks

The paper's definitions and closed-set proof were compared with the intrinsic Lean sources and independently reviewed by the coordinating verifier. The paper states the stronger all-prefix infinite theorem. It includes the actual finite witness, the exact 36-letter move word of the checked periodic array, all twelve exact count slices, and all 55 successor rows. A mechanical transcription check confirms 49 total successor entries, count totals 570/186 and global totals 6840/2232, and exact agreement of the move word with the checked array data.

The count result is explicitly an answer under Pyle's literal chord/move definitions, independent of a type quotient. The effective inverse-move criterion for which permitted chords are approachable is highlighted before the count theorem. The upper bounds are explicitly quotient-dependent and descending-only. Both witnesses' unapproachable start is prominent. Restricted 7/6 bounds, SCC classification, and the 49-edge total are distinguished from named main Lean exports. No modulo-three or pairwise-intersection formalization claim is made. No conjecture-resolution or priority claim is made. The author line and PDF author metadata are GPT-6 Astra. A title-page footnote identifies this as the project AI-author label, not the underlying runtime model or an OpenAI affiliation.

The independent 101-module clean project replay plus separate reviewer audit has completed successfully; this status and the use of installed Lean/Mathlib dependencies are recorded accurately.

## Visual and build checks

- Two final pdfLaTeX passes succeeded.
- Final log contains no warning, overfull box, underfull box, or error.
- All eight pages were visually inspected; the updated count and reproducibility pages were inspected again after the final edits.
- Equations, proof endings, headers, page numbers, table columns, bibliography, and appendix are legible with no clipping or overlap.
- The current render set is exactly `qa/page-1.png` through `qa/page-8.png`.
- Prior page-01 through page-10 and page-9 render files were moved to `qa/superseded-renders/`; they are not the final manuscript.
- `qa/STRUCTURAL_CHECK.json` records machine-readable transcription/build checks.

The paper worker did not run Lean, edit Lean sources, contact authors, publish, or perform remote writes.

## Attribution revision

The user-requested author line and PDF metadata were added, and the README now describes 6840/2232 as new exact numerical answers under the documented limited prior-art search. The PDF remains eight pages. All eight newly rendered pages were visually inspected; pages 2–8 are pixel-identical to the preceding edition. The title-page author and attribution footnote are legible without clipping or overlap. Two PDFLaTeX passes passed without warnings. All protected Lean, wrapper, lock, and replay bytes are unchanged; no Lean compiler was invoked.
