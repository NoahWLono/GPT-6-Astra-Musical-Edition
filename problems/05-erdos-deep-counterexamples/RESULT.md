# Two exact counterexamples to the printed Erdős-deep triple classification

## Result and scope

The fifteen-triple necessity claim in Dukes–Gaede, *Integers* 23 (2023), Conjecture 1, fails when constituents are allowed to be any individually Erdős-deep modular arithmetic progressions, including the endpoint permitted by Gaede's thesis §2.2. There are primitive examples of lengths (10,9,5) and (20,5,5), neither of which is listed.

A stricter variant requiring every constituent length to satisfy k_i≤floor(order(g_i)/2) is not refuted here. The distinction matters: the thesis's standing definition includes a final +1, whereas an earlier general convention omits it. This document does not prove a corrected classification, and it does not assert priority of discovery.

## Definitions

Write AP_n(g,k)={jg mod n:0≤j<k}. For points x,y in Z_n their cyclic distance is min((x−y) mod n,(y−x) mod n). A family is Erdős-deep with total parameter K if its nonzero internal-distance multiplicities are exactly 1,2,…,K−1, each attained at one distance. Distances are counted within constituents, not across different constituents.

The family is primitive if gcd(n,g1,g2,g3)=1. All examples below have generator g1=1. Every constituent has distinct points and satisfies

2(k_i−1)≤n/gcd(n,g_i).

This is the half-order condition under which a constituent has k_i−1 different distance classes with multiplicities 1,…,k_i−1. It includes k_i=floor(order(g_i)/2)+1.

## First counterexample: n=34, lengths (10,9,5)

Take

A=AP_34(1,10)={0,1,2,3,4,5,6,7,8,9},

B=AP_34(6,9)={0,6,12,18,24,30,2,8,14},

C=AP_34(12,5)={0,12,24,2,14}.

The generator orders are 34,17,17. The half-order inequalities are 18≤34, 16≤17, and 8≤17. In particular B is a valid individually Erdős-deep AP of length floor(17/2)+1=9. Direct pair counting gives:

| Distance | A | B | C | Total |
|---:|---:|---:|---:|---:|
| 1 | 9 | 0 | 0 | 9 |
| 2 | 8 | 3 | 2 | 13 |
| 3 | 7 | 0 | 0 | 7 |
| 4 | 6 | 4 | 0 | 10 |
| 5 | 5 | 0 | 0 | 5 |
| 6 | 4 | 8 | 0 | 12 |
| 7 | 3 | 0 | 0 | 3 |
| 8 | 2 | 2 | 0 | 4 |
| 9 | 1 | 0 | 0 | 1 |
| 10 | 0 | 5 | 3 | 8 |
| 12 | 0 | 7 | 4 | 11 |
| 14 | 0 | 1 | 1 | 2 |
| 16 | 0 | 6 | 0 | 6 |

All other positive distances have multiplicity zero. The total column is a permutation of 1,…,13. Therefore {A,B,C} is Erdős-deep with K=14. Also 45+36+10=91=14·13/2, as required by the total number of pairs. Its lengths (10,9,5) are absent from the fifteen-triple list. This proves the claimed necessity statement false under the indicated convention.

## Second counterexample: n=48, lengths (20,5,5)

Take

A=AP_48(1,20)={0,1,…,19},

B=AP_48(6,5)={0,6,12,18,24},

C=AP_48(18,5)={0,18,36,6,24}.

The generator orders are 48,8,8, and the half-order inequalities are 38≤48,8≤8,8≤8. The family distance multiplicities, listed at distances 1,2,…,24, are

(19,18,17,16,15,20,13,12,11,10,9,14,7,6,5,4,3,8,1,0,0,0,0,2).

Their positive entries are exactly 1,…,20. Thus the family is Erdős-deep with K=21. The pair count is 190+10+10=210=21·20/2. Again (20,5,5) is not listed. Both shorter APs have the permitted endpoint length 8/2+1=5.

## Source discrepancy

The published paper's Conjecture 1 (p14) does not state a strict half-order exclusion. The thesis explicitly establishes the individually-Erdős-deep convention with +1 in §2.2 (p16); its Conjecture 4.5 (pp14,42) also displays +1 for the largest constituent. An earlier general convention in Remark 1.10 (p5) uses the stricter bound without +1 and would exclude these examples. The p43 search pseudocode explicitly bounds only the largest length k1 using g1; both examples satisfy that bound. Consequently the printed pseudocode does not explain the omissions, and the actual implementation cause is unknown.

Sources:
- [Published paper](https://math.colgate.edu/~integers/x25/x25.pdf)
- [Thesis record](https://dspace.library.uvic.ca/items/efe2139f-56b2-499c-957b-760fd5b87c4e)
- [Thesis PDF](https://dspace.library.uvic.ca/bitstreams/2f7a7ea4-e7b8-4004-80e8-003554e214bd/download)

## Verification artifacts

ErdosDeepCounterexamples.lean defines modular point lists, recursively enumerates every unordered pair, counts positive cyclic-distance multiplicities, and proves:

- each family's primitivity and all half-order bounds;
- distinctness of the actual modular points;
- that all six constituents separately are Erdős-deep;
- each complete distance histogram;
- the two total Erdős-deep assertions;
- exclusion of the two length triples from the published list;
- the formal negation of the explicitly normalized necessity statement.

Proofs use Lean's kernel reduction, not native_decide, and contain no sorry or additional axioms. The supporting search and separate Python pair-enumeration verifier are in search/. The search was bounded by n≤60 and is not a full classification proof. All individual counterexample claims are independent of search completeness.

Use the portable ./check-lean.sh entry point and REBUILD.md instructions to recheck with Lean 4.32.2 and the pinned Mathlib checkout. The source prints the axiom audit; verification-receipt.json records the results.
