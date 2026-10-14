# Exact statements and limits

For each of 22 explicit five-point difference-table loci, the package proves nonemptiness, bijectivity of the indexed edge map, pairwise distinction of the real solution loci, and maximality against every competing edge permutation in its fixed canonical chamber. The 22 representatives and their number are taken from Erickson–Jones. This is not a new classification.

A general collision criterion reduces possible dominators to permutations within sample collision blocks. There are 97 fiber-permutation choices across the 22 representatives, with at most 32 for one representative. The proof handles all 10! possible competitor permutations through this reduction.

The full intrinsic combinatorial characterization requested in Problem 5.1 remains unresolved here. No theorem proves completeness of the 22-element list, rules out an additional maximal locus, or derives an a priori selection rule. Literature-wide novelty is unestablished.

## Formal declarations

- `DifferenceTableResearch.matching_domination_iff`: general matching-locus inclusion criterion
- `DifferenceTableResearch.IndependentAudit.maps_bijective`: the exact 22 indexed maps are bijections
- `DifferenceTableResearch.IndependentAudit.all_nonempty`: their real loci are nonempty
- `DifferenceTableResearch.IndependentAudit.all_maximal`: their global maximality in the respective fixed chambers
- `DifferenceTableResearch.DistinctMaximal22.pairwise_distinct`: distinction of the indexed real loci

The independent aggregate connects the same indexed maps to the individual maximality results. The correspondence with the source paper's Definition 2.8 is mathematically audited; a separate formal equivalence bridge to the paper's prose is not supplied.
