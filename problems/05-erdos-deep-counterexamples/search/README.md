# Exact finite search and independent pair-enumeration verification

The stated normalized version of Dukes–Gaede Conjecture 1 is false. Two new length triples already occur for n <= 60 when every constituent satisfies 2(k_i-1) <= n/gcd(n,g_i) and the family is primitive.

## Counterexample 1

n=34, lengths (10,9,5), generators (1,6,12), total parameter K=14.

- AP_34(1,10) = {0,1,2,3,4,5,6,7,8,9}.
- AP_34(6,9) = {0,6,12,18,24,30,2,8,14}.
- AP_34(12,5) = {0,12,24,2,14}.

Generator orders are (34,17,17). The constituent bounds read 18<=34, 16<=17, 8<=17. Primitivity follows from generator 1. The nonzero distance-to-multiplicity map is

{1:9, 2:13, 3:7, 4:10, 5:5, 6:12, 7:3, 8:4, 9:1, 10:8, 12:11, 14:2, 16:6}.

Its values are exactly 1 through 13. Also C(10,2)+C(9,2)+C(5,2)=45+36+10=91=C(14,2).

The second constituent has length floor(order/2)+1=9, within the permitted normalization but outside the earlier general convention k_i<=floor(order/2) in thesis Remark1.10; the p43 pseudocode itself only explicitly restricts k1 and does not exclude this example. This is an odd-order boundary case even though 2(k_i-1)<order.

## Counterexample 2

n=48, lengths (20,5,5), generators (1,6,18), total parameter K=21.

- AP_48(1,20) = {0,1,...,19}.
- AP_48(6,5) = {0,6,12,18,24}.
- AP_48(18,5) = {0,18,36,6,24}.

Generator orders are (48,8,8); constituent bounds read 38<=48, 8<=8, 8<=8. Primitivity again follows from generator 1. The nonzero distance-to-multiplicity map is

{1:19, 2:18, 3:17, 4:16, 5:15, 6:20, 7:13, 8:12, 9:11, 10:10, 11:9, 12:14, 13:7, 14:6, 15:5, 16:4, 17:3, 18:8, 19:1, 24:2}.

Its values are exactly 1 through 20. Also C(20,2)+2C(5,2)=190+10+10=210=C(21,2).

Both shorter constituents occupy the even-order boundary excluded by the earlier general strict convention, but not explicitly excluded by the p43 pseudocode. The implementation cause of the omission is unknown.

## Witnesses for all fifteen claimed triples

Each row gives lengths; n; generators, using AP_n(g,k)={jg mod n : 0<=j<k}.

| Lengths | n | Generators |
|---|---:|---|
| (4,4,3) | 11 | (1,2,4) |
| (6,3,3) | 13 | (1,3,5) |
| (6,5,3) | 16 | (1,3,2) |
| (6,6,4) | 17 | (1,3,8) |
| (6,6,6) | 20 | (1,2,3) |
| (7,7,3) | 23 | (1,5,3) |
| (9,4,3) | 20 | (1,3,8) |
| (8,7,4) | 29 | (1,12,12) |
| (8,8,5) | 38 | (1,7,1) |
| (10,6,4) | 23 | (1,7,5) |
| (12,4,4) | 26 | (1,6,6) |
| (13,5,3) | 29 | (1,4,12) |
| (13,7,4) | 34 | (1,5,3) |
| (16,5,4) | 40 | (1,4,15) |
| (21,6,4) | 48 | (1,5,18) |

## Files and reproduction

- search.cpp: C++17 search, compile with `g++ -O3 -std=c++17 search.cpp -o search`.
- Run `./search 6 60 > results_6_60.csv 2> log_6_60.txt`.
- verify.py: independent verifier using explicit AP point sets and unordered pairs, not the search's difference-weight formula. Run `python verify.py`.
- verified_witnesses.json: all seventeen first witnesses with explicit APs, generator orders, and distance multiplicities.
- results_6_60.csv: all 649 canonical representative hits.
- Console progress output is not distributed; rerunning the search generates it locally.

Search checks all n=6,...,60, k_i>=3, every admissible constituent length, and all primitive generator tuples up to unit and sign normalizations. Triangular count and support constraints prune impossible lengths; a sum-of-squares condition prunes generator choices before exact multiplicity verification. All 649 output rows were independently verified by explicit pair enumeration. No running job remains.

Normalization: unit multiplication is transitive on residues with the same gcd with n, so choose g1=gcd(n,g1), a divisor of n. Sign choices permit 1<=g_i<=floor(n/2). When the largest lengths are tied, designate a constituent having the least generator gcd as the first before unit normalization; hence the first generator can be chosen <= the other tied generators. Other equal-length generators can be sorted. These symmetries preserve cyclic-distance multiplicities up to relabeling.

The CSV 'boundary' field detects only exact equality 2(k_i-1)=order. It does not flag the odd-order +1 band, so use generator orders in the JSON to identify the full omitted band.

Finite search does not prove a classification or absence of further triples. These individual exact counterexamples do disprove the stated fifteen-triple classification under the given admissibility conditions.
