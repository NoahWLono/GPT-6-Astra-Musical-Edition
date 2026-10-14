# Independent audit: Erdős-deep triple counterexamples

## Verdict

The two examples are valid counterexamples to the **necessity of the fifteen length triples in the printed Dukes–Gaede (2023), Conjecture 1**. This conclusion follows from the paper's own definition of a family distance multiset and Erdős-deepness, and remains true after imposing primitivity, minimum constituent size three, distinct AP points, and separate Erdős-deepness of each constituent.

The examples do **not** refute a revised claim that imposes `k_i ≤ floor(order(g_i)/2)` on every constituent. Their exceptional lengths are the final admissible endpoint, `floor(order/2)+1`. No exhaustive classification, priority claim, author-intent claim, or implication for the classical planar Erdős problem is established by this audit.

## Verified mathematics

An independent Python implementation enumerates unordered pairs of actual modular points and computes their distance as `min(abs(x-y), n-abs(x-y))`. It does not use the search's triangular-weight shortcut or Lean's modular-subtraction implementation.

- `n=34`, generators `(1,6,12)`, lengths `(10,9,5)`: exactly 91 pairs. Complete distance histogram at distances 1 through 17 is `[9,13,7,10,5,12,3,4,1,8,0,11,0,2,0,6,0]`. Its positive multiplicities are exactly 1 through 13. The three individual multiplicity sets are 1 through 9, 1 through 8, and 1 through 4.
- `n=48`, generators `(1,6,18)`, lengths `(20,5,5)`: exactly 210 pairs. Complete distance histogram at distances 1 through 24 is `[19,18,17,16,15,20,13,12,11,10,9,14,7,6,5,4,3,8,1,0,0,0,0,2]`. Its positive multiplicities are exactly 1 through 20. The three individual multiplicity sets are 1 through 19, 1 through 4, and 1 through 4.
- Every point list is duplicate-free. All pair distances are positive and at most `floor(n/2)`. In particular the second example correctly includes the antipodal distance 24 with total multiplicity 2.
- Both families are primitive because their first generator is 1. The actual size triples are absent from the published list, whose fifteen tuples were independently checked against the source PDF.

## Lean verification

A frozen copy of the original `ErdosDeepCounterexamples.lean` was compiled from source in this audit directory, without reusing its supplied `.olean`.

- Lean 4.32.2, compiler commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`; working tree was clean when recorded.
- Both counterexample theorems and `not_normalizedClassification` use only standard axioms `propext` and `Quot.sound`.
- The histogram, individual constituent-depth, and endpoint theorems have no axiom dependencies.
- No `sorry`, extra axiom declaration, `native_decide`, unsafe implementation, or external evaluation bypass occurs in the source.
- An independent importing harness prints the exported theorem statements/proof terms and proves exact total pair counts, range/positivity of every enumerated distance, zip-list lengths, and actual AP-list lengths. These additional harness theorems have no axiom dependencies.

The formalization uses lists, not a separate abstract finite-set distance library. Its computational interpretation is sound here: `apPoints` computes actual residues, `Nodup` is separately proved, the recursion pairs each head with precisely its later entries, and the distance scan includes every possible positive cyclic distance. Natural-number subtraction in `cyclicDistance` is safe on these residue representatives. Equal-length generator/length lists prevent zip truncation; the importing harness certifies that fact concretely.

The source hashes in `source-sha256.txt` identify precisely the original files covered. Other workers may subsequently correct the prose and comments; those updates are not silently included in this frozen audit.

## Source corrections required in the original prose

1. **Pseudocode scope:** thesis printed p43, line 3, explicitly bounds only `k1` using `g1`. Both counterexamples meet that bound (`10≤17` and `20≤24`). It is incorrect to say this displayed pseudocode itself excludes the examples or establishes why the original search missed them. The historical implementation cause remains unknown.
2. **Page citation:** Remark 1.10 is printed **p5** (PDF page 12), not printed p4.
3. **Logical wording:** the comment describing `NormalizedClassification` as a “stronger-than-literal” statement should instead say a restricted-domain version with additional hypotheses. A universally quantified implication with a stronger antecedent is a weaker classification assertion. Refuting it gives a more constrained counterexample.

These corrections do not affect the counterexamples or their Lean proofs.

## Exact source reconciliation

- Published paper, printed pp2–3: ordinary modular APs, cyclic distances, and multiset union of internal distance multisets define the objects. Printed p3, Theorem 1, explicitly contains the final `+1` in the individual Erdős-deep AP bound.
- Published paper, printed p14, Conjecture 1: fifteen length triples, with no displayed strict half-order hypothesis. Both examples contradict its necessity direction.
- Thesis, printed p5, Remark 1.10: a general strict convention without `+1` is stated. Applying this convention to each constituent excludes the examples.
- Thesis, printed p16, §2.2: the individually-Erdős-deep convention explicitly permits `+1` for each constituent.
- Thesis, printed p14 and pp42–43, Conjecture 4.5: the largest-constituent bound explicitly includes `+1`; the same fifteen length triples appear.
- Thesis, printed p43, simplified pseudocode: its displayed largest-constituent bound omits `+1`, but does not exclude the examples. It does not explicitly encode strict bounds for all constituent generators.

Source PDFs were opened online and relevant local PDF pages were visually inspected. Primary sources:

- https://math.colgate.edu/~integers/x25/x25.pdf
- https://dspace.library.uvic.ca/bitstreams/2f7a7ea4-e7b8-4004-80e8-003554e214bd/download

## Artifacts

- `frozen/`: original audited Lean source and independent import harness; compiled objects and superseded prose are not distributed.
- The axiom conclusions are recorded in this report and the top-level verification receipt. Raw compiler/export console logs are omitted; the published source and importing harness reproduce those checks.
- `independent-count.py`, `independent-count.json`: separate actual-point pair count and full constituent data.
- `environment.txt`, `source-sha256.txt`: reproducibility identifiers.
- Source-page PNGs/text were inspected during the audit but are not redistributed. Original source links and the reconciliation above identify the evidence.

The separate claim about all 649 bounded-search hits was not rerun in this audit; no individual counterexample or printed-claim refutation depends on it.
