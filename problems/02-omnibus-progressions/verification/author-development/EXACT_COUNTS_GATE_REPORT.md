# Exact image count completion gate

Completed 2026-10-13 20:17 UTC; compiler slot 2 released.

All 37 processes passed. Aggregate actual child CPU: 141.223 seconds of 240 authorized. Maximum process CPU: 8.293 seconds. Maximum RSS: 1856928 KiB. Each process used Lean 4.32.2, -j1, 19.5-second CPU watchdog, 20-second hard CPU, 35-second wall watchdog, 2 GiB resident-memory limit, 64 MiB output and 4 GiB free-disk floor. No cap was reached. Historical combined compiler CPU including prior failures: 473.893 seconds.

## Exact checked exports (namespace Omnibus)

```lean
theorem normalized_image_count_exact :
  Nat.card {t : PCTriple // inImage (unpackZero t) = true} = 570

theorem normalized_approachable_count_exact :
  Nat.card {t : PCTriple // chord (unpackZero t) = true ∧ inImage (unpackZero t) = true} = 186

theorem global_image_count_exact :
  Nat.card {c : Chord // ActualImage c} = 6840

theorem global_approachable_count_exact :
  Nat.card {c : Chord // chord c = true ∧ ActualImage c} = 2232
```

Here ActualImage c is `∃ d : Chord, chord d = true ∧ ∃ v : Fin 3, step v d = c`. Thus the results count actual ordered pitch-class endpoints of the three descending-bass moves from intrinsically recognized permitted chords, and their intersection with permitted chords. Endpoint image membership does not require the endpoint to be a permitted chord; the second theorem adds precisely that restriction.

All four exports report only `[propext, Classical.choice, Quot.sound]`. No sorry, custom graph axioms, native_decide, or external numerical oracle is used. The finite list generator is connected to intrinsic membership by ImageEnumerationSemantics; exact raw-list identities are kernel equalities; cell counts use kernel decide; partition/cardinality and transposition-factor equivalences are proved.

ExactImageCounts source SHA256: `1c40cd5087dff803a45e9c30faa2e2d723cdab48d8228bff20a7ca815ff895e9`.
Object SHA256: `7b8ce400878c2c4c6419a7fd75c6849610c5294b3598fdb7eee545105f3dff45`.

## Process receipts

Attempt sources, logs and JSON receipts are preserved under countcompletion_gate/. Earlier capped gates remain preserved. COMPLETE_REBUILD_MANIFEST.json records the complete local dependency order, source/object hashes and receipt consistency for sharp bounds, the stronger infinite-range theorem, and exact counts. Independent clean replay is still required. After the gate, obsolete status comments were corrected in 50 sources, with no proof edits; comment_cleanup/ preserves the before bytes and hash changes. COMPLETE_REBUILD_MANIFEST.json now freezes the cleaned bytes and explicitly marks those older receipt mismatches. The independent verifier owns fresh replay.

| Module | CPU seconds | Peak RSS KiB |
|---|---:|---:|
| ImageCountSlice4 | 2.262 | 1852384 |
| ImageCellBlock5_0 | 2.933 | 1590604 |
| ImageCellBlock5_1 | 3.057 | 1594132 |
| ImageCellBlock5_2 | 4.378 | 1613628 |
| ImageCellBlock5_3 | 4.634 | 1648540 |
| ImageCountSlice5 | 2.074 | 1853024 |
| ImageCellBlock6_0 | 3.162 | 1593400 |
| ImageCellBlock6_1 | 3.511 | 1630336 |
| ImageCellBlock6_2 | 3.290 | 1614636 |
| ImageCellBlock6_3 | 4.711 | 1687168 |
| ImageCountSlice6 | 1.988 | 1852476 |
| ImageCellBlock7_0 | 3.299 | 1624632 |
| ImageCellBlock7_1 | 7.491 | 1624572 |
| ImageCellBlock7_2 | 8.293 | 1588488 |
| ImageCellBlock7_3 | 4.791 | 1619948 |
| ImageCountSlice7 | 2.968 | 1847008 |
| ImageCellBlock8_0 | 2.578 | 1613248 |
| ImageCellBlock8_1 | 4.533 | 1629260 |
| ImageCellBlock8_2 | 3.793 | 1609004 |
| ImageCellBlock8_3 | 3.972 | 1628180 |
| ImageCountSlice8 | 1.907 | 1852648 |
| ImageCellBlock9_0 | 3.006 | 1592928 |
| ImageCellBlock9_1 | 5.174 | 1646940 |
| ImageCellBlock9_2 | 3.645 | 1619592 |
| ImageCellBlock9_3 | 4.207 | 1591104 |
| ImageCountSlice9 | 2.244 | 1852376 |
| ImageCellBlock10_0 | 5.067 | 1613172 |
| ImageCellBlock10_1 | 7.000 | 1653608 |
| ImageCellBlock10_2 | 4.354 | 1627832 |
| ImageCellBlock10_3 | 3.480 | 1600056 |
| ImageCountSlice10 | 1.983 | 1852852 |
| ImageCellBlock11_0 | 3.626 | 1606032 |
| ImageCellBlock11_1 | 4.931 | 1631420 |
| ImageCellBlock11_2 | 4.077 | 1627180 |
| ImageCellBlock11_3 | 4.102 | 1613720 |
| ImageCountSlice11 | 2.315 | 1852616 |
| ExactImageCounts | 2.387 | 1856928 |

## Scope retained

The 8/7 bounds use the explicit bass-relative upper-multiset quotient and permit entrance chords. Their sharp witnesses start at the zero-indegree type 036. Requiring approachability at the start excludes them; contextual 7/6 bounds are not yet Lean exports. This work does not settle Pyle’s undefined extension/sonority conventions or establish originality. Descending-only moves are used; mixed directions are excluded.
