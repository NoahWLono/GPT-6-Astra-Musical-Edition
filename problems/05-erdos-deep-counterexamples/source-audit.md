# Source audit and exact scope

## Sources

- Peter J. Dukes and Tao Gaede, *Families of modular arithmetic progressions with an interval of distance multiplicities*, Integers 23 (2023), #A25. https://math.colgate.edu/~integers/x25/x25.pdf
- Tao Gaede, *Erdős-Deep Families of Arithmetic Progressions*, MSc thesis, University of Victoria (2022). https://dspace.library.uvic.ca/items/efe2139f-56b2-499c-957b-760fd5b87c4e ; PDF https://dspace.library.uvic.ca/bitstreams/2f7a7ea4-e7b8-4004-80e8-003554e214bd/download

The local PDF copies have been extracted with `pdftotext -layout`. The page references below are the documents' printed page numbers.

## Three different formulations must not be conflated

1. The published Conjecture 1 (paper, p14) lists fifteen length triples, without an explicit lower bound on the shortest length, primitivity condition, or upper bound on each constituent length. It is stated in a context of arithmetic-progression families.
2. The thesis's standing convention in §2.2 (p16) explicitly concerns families whose constituents are individually Erdős-deep. It specifies k_i ≤ floor(n/(2 gcd(n,g_i)))+1 and k_1≥...≥k_s≥3. This is equivalent to 2(k_i−1)≤n/gcd(n,g_i). These admissible APs can wrap geometrically; it is the distinctness of their internal distance classes that matters.
3. The thesis has a stricter convention earlier, in Remark 1.10 (p5), which would exclude the examples if applied to every constituent. Its triple-search pseudocode (p43) explicitly bounds only the largest length k1 using g1, without the final +1. Both examples satisfy that displayed largest-length bound, so the pseudocode itself does not explain their omission.

The thesis's Conjecture 4.5 (pp14,42) explicitly prints the +1 bound for the largest constituent, in addition to the standing §2.2 convention. Its search pseudocode explicitly enforces primitive gcd(n,g1,g2,g3)=1 in the nonunit branch; when g1=1 this is automatic. Primitivity is essential for its claim that some triples have only finitely many moduli: scaling n and every generator embeds any example into arbitrarily large moduli with unchanged multiplicities.

## Exact conclusion

There are counterexamples to the printed fifteen-triple classification, including under the stronger, well-defined interpretation in which every AP is individually Erdős-deep and the family is primitive. The counterexamples are (n; lengths; generators)=(34;10,9,5;1,6,12) and (48;20,5,5;1,6,18).

Both use a shorter constituent of length floor(order/2)+1. Thus they do not disprove a modified conjecture that additionally requires every k_i≤floor(order_i/2). That stricter classification is neither proved nor disproved by the present work. The source conventions differ, but the actual implementation cause of the omission is unknown. In particular, the displayed search restriction on k1 does not exclude these examples, and we do not infer a restriction on every k_i from that pseudocode.

## Independent checks

The search uses triangular-weight distance formulas. A separate Python verifier enumerates unordered pairs of actual modular points. A third calculation was run independently by the parent assistant. The Lean file separately counts unordered pairs by a structurally recursive traversal of distinct modular-point lists. None of the individual counterexamples relies on exhaustiveness of the search.

The bounded search through n≤60 found the fifteen claimed length triples and the two additional ones, with 649 representative hits, all checked by the independent pair enumerator. This is finite evidence only, not a corrected classification theorem.
