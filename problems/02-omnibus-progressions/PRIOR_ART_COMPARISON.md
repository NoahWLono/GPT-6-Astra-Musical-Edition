# Prior art audit of the omnibus image counts

Audit date: 13 October 2026, UTC. Scope: the two numerical image questions in Pyle (2025), the author's current supplement and available history, exact-number searches, and discoverable later citations. This is a bibliographic and semantic audit, not an independent replay of the local formal proof.

## Conclusion

**The original publication explicitly leaves the two numerical image questions unanswered.** The local results 6840 and 2232 address those numerical questions with the original ordered-chord domain and descending-bass maps. No matching published solution was located in this targeted audit. The available author supplement contains no later image-count computation. These findings support a carefully scoped contribution claim, but do not establish priority or that the questions remain unsolved everywhere.

## Exact source mapping

Pyle, Hayden. *Generalized Omnibus Progressions: A Mathematical Formalization of Harmonic Progressions Exhibiting Semitonal Contrary Motion and Tertian Sonorities*. Journal MusMat IX (2025), 27–41. [Publisher record](https://musmat.org/journal/v9/02-Pyle.html); [published PDF](https://musmat.org/journal/v9/02-Pyle.pdf). DOI: 10.46926/musmat.2025v9.27-41.

The following maps the source to the local statements:

- Page 27: objects are ordered four-note pitch-class segments `(b,t,a,s)` in `R = (Z/12Z)^4`, retaining voice positions and repetitions.
- Page 28, Definitions 4–5: `Q` comprises segments admitting a permutation with consecutive modular intervals consisting of exactly one 0 and two members of `{3,4}`, or four distinct entries admitting three consecutive intervals in `{3,4}`.
- Page 30, Definition 6: `f_T(b,t,a,s)=(b−1,t+1,a,s)`, `f_A(b,t,a,s)=(b−1,t,a+1,s)`, and `f_S(b,t,a,s)=(b−1,t,a,s+1)`, modulo 12, with domain `Q` and codomain `R`.
- Page 41, Section V: after reporting `|R|=20736` and `|Q|=3240`, Pyle asks the size of the combined image, allowing collisions between different maps and inputs, and the number and identity of approachable members of `Q`.

Thus the exact numerical targets are

1. `|I| = 6840`, where `I = f_T(Q) ∪ f_A(Q) ∪ f_S(Q)`.
2. `|Q ∩ I| = 2232`.

The source's collision discussion supports this union reading of its `Im f_V` notation. Neither target identifies chords up to transposition, permutes upper voices after counting, adds root labels, or requires an interpretation of extension. The project's sharp 8/7 bounds do require its explicitly selected quotient and progression conventions; this audit does not convert them into a resolution of Conjecture 1.

The local exports `Omnibus.global_image_count_exact` and `Omnibus.global_approachable_count_exact` in `ExactImageCounts.lean` have precisely the corresponding cardinality forms. `PROOF.md` and `EXACT_COUNTS_GATE_REPORT.md` report their verification; they were read, not independently compiled here. Importantly, 2232 alone answers the numerical part of the second question. For the identity part, an explicit criterion is: an endpoint `c∈Q` is approachable exactly when at least one of `c+(1,−1,0,0)`, `c+(1,0,−1,0)`, or `c+(1,0,0,−1)` belongs to `Q`, modulo 12. This follows by inverting the three maps; a reader-facing classification or list would make that part more useful.

## Author supplement and history

The [repository linked by the paper](https://github.com/Beethoven119/Generalized-Omnibus-Progression-Algorithms/) was inspected through GitHub's read-only API on the audit date. The current notebook was parsed as JSON; none of its code was executed.

- The [contents endpoint](https://api.github.com/repos/Beethoven119/Generalized-Omnibus-Progression-Algorithms/contents) returns one file, `GOP Algorithms.ipynb`, 23530 bytes, blob `3bc610f50cd5e93d649e28d03d9f0788b0e0fd8a`.
- The [commit list](https://api.github.com/repos/Beethoven119/Generalized-Omnibus-Progression-Algorithms/commits?per_page=100) returns one root commit: [`262ae19b9aba23e01465d1bde83da36b333c1f4e`](https://github.com/Beethoven119/Generalized-Omnibus-Progression-Algorithms/commit/262ae19b9aba23e01465d1bde83da36b333c1f4e), dated 29 November 2025, 21:46:26 UTC, with no parents.
- The [branch list](https://api.github.com/repos/Beethoven119/Generalized-Omnibus-Progression-Algorithms/branches?per_page=100) returns only `main`, at that commit. The [all-state issue list](https://api.github.com/repos/Beethoven119/Generalized-Omnibus-Progression-Algorithms/issues?state=all&per_page=100) and [release list](https://api.github.com/repos/Beethoven119/Generalized-Omnibus-Progression-Algorithms/releases?per_page=100) are empty.
- The [immutable notebook](https://github.com/Beethoven119/Generalized-Omnibus-Progression-Algorithms/blob/262ae19b9aba23e01465d1bde83da36b333c1f4e/GOP%20Algorithms.ipynb) has six cells: three interactive recognition cells, exhaustive triad/seventh enumeration, file-based recognition, and an empty cell. Its saved enumeration output is 20736 tested, 1440 triads, 1800 seventh chords. It neither implements the three omnibus moves nor calculates their images. Neither target number occurs in source or saved outputs.
- The local historical notebook's independently recomputed Git blob hash matches the current remote blob exactly.

Therefore the available repository history supplies no later amendment answering the image questions. This conclusion concerns visible reachable history, not deleted history, private work, or other repositories. A tags-list request was rejected as an unsupported connector endpoint and supplies no evidence about tags.

## Other sources and citation checks

1. [Pyle's April 25, 2025 conference abstract](https://graduate.missouristate.edu/_Files/_EIDF/EIDF2025_AbstractBooklet.pdf), printed page 57, poster B34, predates the journal paper. It discusses the framework and three-to-six observation, but provides neither target count. Both numbers were also absent from the searchable PDF text. This is earlier exposition, not a later solution.
2. [Fiore et al., arXiv:2507.20811](https://arxiv.org/abs/2507.20811), including Pyle as coauthor, currently lists only v1, submitted July 28, 2025. The [full text](https://arxiv.org/html/2507.20811v1), particularly the introduction and Examples 3.2–3.4, studies group actions on selected triad/seventh orbits and omnibus voicing matrices. It does not supply the literal image counts. Searches of its full text found neither 6840 nor 2232, 3240, or the journal article's title. It predates the journal article and is cited by it; it should not be described as a later citing solution.
3. [Rockwell, “Birdcage Flights” (2009)](https://www.mtosmt.org/issues/mto.09.15.5/mto.09.15.5.rockwell.html), especially paragraphs 5 and 16–20, concerns inter-cardinality voice-leading graphs with different modeling choices. The inspected article supplies neither target count; both numbers are absent from its searchable text. Its existing omnibus networks remain relevant background.
4. The [ResearchGate record](https://www.researchgate.net/publication/398792323_Generalized_Omnibus_Progressions_A_Mathematical_Formalization_of_Harmonic_Progressions_Exhibiting_Semitonal_Contrary_Motion_and_Tertian_Sonorities) displayed zero resolved citations in the retrieved page. This is only that index's displayed state; the search service marked the page as crawled four months earlier. It is not evidence of zero citations worldwide or a current authoritative citation total.
5. Exact-title searches restricted to arXiv, Semantic Scholar, Google Scholar, and OpenAlex returned no results. Direct Google Scholar and DOI-based Crossref, OpenAlex, and Semantic Scholar API opens produced tool retrieval errors. No authoritative, exhaustive citing-paper list was obtained. The [author's homepage](https://www.haydenpyle.com/) provided no relevant follow-up link in its retrieved navigation.

## Reproducible web search log

All searches below were performed on 13 October 2026 UTC. Searches returned the original publication, related earlier literature, unrelated fallback matches, or no results. No returned item verified a later solution with the same domain, maps, and targets. Quoted query syntax is recorded verbatim; returned fallback results sometimes did not satisfy all quoted terms.

- `"Generalized Omnibus Progressions" Hayden Pyle`
- `"Generalized Omnibus Progressions"`
- `"10.46926/musmat.2025v9.27-41"`
- `"Generalized Omnibus" "6840"`
- `"Generalized Omnibus" "2232"`
- `"Generalized Omnibus Progressions" "6840"`
- `"Generalized Omnibus Progressions" "2232"`
- `"omnibus" "6840" "2232"`
- `"omnibus" "6,840"`
- `"omnibus" "2,232" chords`
- `"omnibus progression" "6840"`
- `"omnibus progression" "2232"`
- `"Generalized Omnibus Progressions" -site:musmat.org`
- `"Hayden Pyle" omnibus image count`
- `"musmat.2025v9.27-41" citations`
- `"Generalized Omnibus Progressions" Pyle 2026`
- `"Generalized Omnibus Progressions" citations -site:musmat.org`
- `"Hayden Pyle" "omnibus" solution`
- `"musmat.2025v9.27-41" -site:musmat.org`
- `"Generalized Omnibus Progressions" site:semanticscholar.org`
- `"Generalized Omnibus Progressions" site:scholar.google.com`
- `"Generalized Omnibus Progressions" site:openalex.org`
- `"Generalized Omnibus Progressions" site:arxiv.org`
- `"Generalized Omnibus Progressions" "image"`
- `"Generalized Omnibus Progressions" "approachable"`
- `"Generalized Omnibus Progressions" "proof"`
- `"Generalized Omnibus Progressions" "solution"`

## Claim suitable for a manuscript

“We give exact answers, 6840 and 2232, to the numerical image questions posed in Section V of Pyle (2025), using the ordered pitch-class segments and omnibus functions of Definitions 4–6. Our literature search through 13 October 2026 did not locate a previously published answer.”

Use this only alongside the independently reviewed mathematical proof. Avoid “first solution,” “previously unsolved,” or “settles Pyle's conjecture”: incomplete indexing, retrieval failures, alternative terminology, unpublished work, and the distinct extension issue prevent those stronger conclusions.
