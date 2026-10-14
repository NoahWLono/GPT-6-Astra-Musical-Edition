# Independent audit result

PASS on 14 October 2026.

The frozen formal source was rebuilt in an isolated audit directory, without reusing any project object file. Lean 4.32.2 and the pinned mathlib cache were reused. Compilation completed with exit status 0 in 74.84 seconds. Both explicit negated-conjecture theorems depend only on standard Lean/mathlib axioms.

The audit independently checked the source conventions, multiplicity-sensitive interval definitions, distinct shared subset types, whole-set inequivalence, all source and target T/I representatives, the unbounded integer-axis reduction, and the printed integer-multiple T-shift definition. No remaining semantic or proof gap was identified. Independent enumeration agrees with both concrete examples.

The parameterized t ≥ 6 pitch family was reviewed as an ordinary mathematical proof. It is explicitly outside the current formalized theorem scope.

Formal source SHA256:

a884ebb6566c9920f3890c3b9b331a84c7e4a168404482847992a59b92217ace

Receipts and exact exported theorem statements are included in this directory. The audit makes no claim about novelty or publication priority.
