# Infinite-range and count-semantics gate: 2026-10-13 19:47–19:48 UTC

## Checked strengthening

InfiniteRangeBound passed. Omnibus.universal_infinite_seven_type_bound proves, for EVERY infinite admissible ordered-chord walk c and EVERY N,
`((Finset.range N).image (fun k => sonority (c k))).card ≤ 7`.

Omnibus.infinite_seven_type_bound_is_sharp supplies an actual infinite admissible walk satisfying this all-prefix bound and attaining seven distinct types in its first seven positions. Both printed axiom sets are exactly propext, Classical.choice, Quot.sound. These are direct corollaries of the already checked closed-set argument and sharpness witness, not new graph assumptions.

Source SHA-256: `3c715ac3f3b253532bbb3100f5e3519ebc4b9cb14b32b710e3c87f47103137e6`. Olean SHA-256: `234a5603a2123df2770c015c2335ac4018f95d6e445440f73feac6a9999e446e`.

## Checked count prerequisites

BassPackedEquiv passed: the bass-normalized Fin-12 quadruple map has explicit two-sided inverse, with unpacking/translation identities. BassPredicateEquiv passed: it restricts this equivalence to every transposition-invariant chord predicate. Printed axioms are propext and Quot.sound. These are genuine equivalences, but numerical image cardinalities remain unchecked.

BassCardinality attempt 1 failed at its low tactic-heartbeat guard. Attempt 2 hit the 2-GiB RSS watchdog while specializing Fintype cardinality to the concrete image predicate. The gate stopped immediately and released slot 2. No subsequent enumeration semantics or numerical slice process ran.

## Resources

Aggregate actual child CPU: **17.699 seconds** of 90 authorized, including both failures. Peak RSS **2102360 KiB**, an observed polling overshoot at the 2097152-KiB RSS watchdog threshold; that attempt was killed. All other per-process caps were unchanged. No limit was relaxed.

## Every attempt

- InfiniteRangeBound, 2026-10-13T19:47:39.763666+00:00: exit 0; CPU 1.562s; wall 1.587s; RSS 1645308 KiB; memory stop False.
  Source `3c715ac3f3b253532bbb3100f5e3519ebc4b9cb14b32b710e3c87f47103137e6`; olean `234a5603a2123df2770c015c2335ac4018f95d6e445440f73feac6a9999e446e`.
- BassPackedEquiv, 2026-10-13T19:47:41.463663+00:00: exit 0; CPU 2.013s; wall 2.020s; RSS 1210832 KiB; memory stop False.
  Source `c56dd46cecd054687bc0e2fca7e9990a27736b9046002af120ffa9c7161628e6`; olean `33bead910f2d6f87d5da306adfaec6535f8562e8f3d7e3556e8c10b4f47cf1c7`.
- BassPredicateEquiv, 2026-10-13T19:47:49.931615+00:00: exit 0; CPU 1.132s; wall 1.168s; RSS 1186988 KiB; memory stop False.
  Source `464f83a6cdc594d4b339e9062d239a120dde3287ec559269a20fa64340c9ad50`; olean `6b03cbc920d0e1251c479b914cdc09f3cdf94b6f7452d7fced598a8d70603670`.
- BassCardinality, 2026-10-13T19:47:51.229292+00:00: exit 1; CPU 6.882s; wall 6.919s; RSS 1774104 KiB; memory stop False.
  Source `4aaaef95ff82395f4efc424a93d44bdfdf183d1771df8f5777651dd1eae4ef0f`; olean `None`.
- BassCardinality, 2026-10-13T19:48:23.936464+00:00: exit -9; CPU 6.110s; wall 6.123s; RSS 2102360 KiB; memory stop True.
  Source `bdac9302e5e79b1565ab1ee8ef70db0b72a81bbfb3f572c6273360c5aa55481f`; olean `None`.

All attempt sources/logs/receipts are preserved in count_gate. No result is inferred from either failed BassCardinality attempt, including any intermediate theorem printed before the error. Successful source header comments remain frozen and are superseded by this audit.

## Source-only repair and completion

The missing disjoint-slice cardinality bridge is now written in DisjointSliceCardinality and ImageSliceSemantics: an explicit equivalence sends a packed zero-bass chord to its uniquely determined tenor-indexed slice and reconstructs it. Each slice is deduplicated, so its finite set cardinal equals list length. This proves summation over disjoint slices without assuming disjointness.

BassNatCardinality replaces concrete executable Fintype filter instances with semantic Nat.card, using the checked predicate equivalence. This is intended to avoid the failed instance-normalization route; it remains uncompiled. All counted types are finite subtypes of products of Fin 12. ActualChordCardinality relates these encoded types to actual intrinsic ordered-chord image sets. ExactImageCounts assembles the intended global cardinalities 6840 and 2232. Every new module remains source only.

A fresh independent literal-definition Python audit checked all twelve proposed slice counts and exact set equality between canonical generation and actual full-space images. COUNT_TARGET_AUDIT.json records 3240/6840/2232 globally, 270/570/186 at bass zero, every slice, runtime and source hash. This is supporting evidence, not a Lean proof of counts.

The entrance-boundary and Pyle-semantics qualifications remain unchanged.
