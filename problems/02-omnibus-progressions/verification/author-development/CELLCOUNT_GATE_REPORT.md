# Fine-cell pilot gate: 2026-10-13 20:07–20:09 UTC

Checked ImageCellDefinitions and ImageCellPartition give an exact second-coordinate partition of each tenor slice. ImageRawCertificate checks the literal raw source/image generator lists against the intrinsic definitions; those lists are proved equalities, not assumptions. All twelve alto cells at tenor 4 are now checked. Optimized three-cell blocks take roughly 3–6 CPU seconds.

ImageCountSlice4 recombination hit the RSS watchdog before a successful artifact. The gate stopped immediately and slot 2 was released. No tenor-4 aggregate count is yet accepted, despite all its cells being checked. The next source uses explicit finite-index branch proofs and pointwise sum congruence to avoid closed-term normalization during generic rewriting; the same correction is applied to ExactImageCounts. No retry was started after the cap.

Aggregate actual child CPU: **35.804 seconds** of 180 authorized. Peak RSS: **2105172 KiB**, a polling overshoot of the 2097152-KiB watchdog. No resource limit was increased.

## Every attempt

- ImageCellDefinitions, 2026-10-13T20:07:34.421991+00:00: exit 0; CPU 1.523s; wall 1.578s; RSS 1562536 KiB; RSS stop False.
  Source `c2f9e71c8782365a667324fc30f7935ceba13b801b52a2b33816068e03ca3636`; olean `90a1dc5cdb07a6492d243382c6ede8a11d8ab78d406ab406594fec81e3e053be`.
- ImageCellPartition, 2026-10-13T20:07:36.127158+00:00: exit 0; CPU 4.427s; wall 4.446s; RSS 1840464 KiB; RSS stop False.
  Source `aee3ad78b7e7e94675971889c48a419c90e9d07abb030a27430550887ab62fb5`; olean `b966959925baf159693ff9b3bfc7fce696e11b5c87b81dcf45aacad4e28335af`.
- ImageCellBlock4_0, 2026-10-13T20:07:46.881007+00:00: exit 0; CPU 8.772s; wall 8.815s; RSS 1706596 KiB; RSS stop False.
  Source `6f06600b4a330f7742a10bf6e673d1eb21f958a52542a371fbeb84713021aa22`; olean `c63fc49877cc776a359e1d06c324a2fe5ff886a350151f8b476a07c8497f2f49`.
- ImageRawCertificate, 2026-10-13T20:08:45.436068+00:00: exit 0; CPU 4.971s; wall 5.016s; RSS 1673828 KiB; RSS stop False.
  Source `98b0bdab810f69a9688293a54b49f82c0ec54a98734d39084bf46bb1c0f61303`; olean `095b765dc92f2b6b4d578e772be0dd14ac908b9d44d7f07e5ca9d975dd986fb2`.
- ImageCellBlock4_1, 2026-10-13T20:09:04.976760+00:00: exit 0; CPU 3.067s; wall 3.134s; RSS 1599340 KiB; RSS stop False.
  Source `623f3abe39a3e63b9f522c248f19fac894ffa517d008fd9b8e9ea314776be4ef`; olean `4923c5ef932cc58193b01e651c8acc0f57260ca0f35ebfab69b1c2814e8f37d7`.
- ImageCellBlock4_2, 2026-10-13T20:09:26.341489+00:00: exit 0; CPU 3.725s; wall 3.760s; RSS 1612628 KiB; RSS stop False.
  Source `a32f54a3cdc7f922b00f8b0ad897e953866910d1cffad70da64c701deaecaee1`; olean `4912454d3a9579b76687753a01d1fec7dfdd4d034ff387e977eecda3dc540d10`.
- ImageCellBlock4_3, 2026-10-13T20:09:30.212842+00:00: exit 0; CPU 5.971s; wall 6.004s; RSS 1629428 KiB; RSS stop False.
  Source `e3169f7b70f363287f6cbb16f4705249a80541a779be74ca4e609ebf95f86596`; olean `7294f5a1b12548c70fcebf2c9c4f4b21c8fd201f5b1c515fad1c34a6f2429955`.
- ImageCountSlice4, 2026-10-13T20:09:36.332992+00:00: exit -9; CPU 3.348s; wall 3.361s; RSS 2105172 KiB; RSS stop True.
  Source `e9fee9ed71cd4a79b7c89beb8f46c493c64e1e869c70aaa1f61fcb668a9ed70c`; olean `None`.

All attempt inputs/logs/receipts are frozen in cellcount_gate. The failed recombination source is preserved there while the current source has been revised. SourceRaw equality is axiom-free; imageRaw equality and image cell counts use propext; optimized approachable cell counts use propext and Quot.sound; exact partition semantics use propext, Classical.choice and Quot.sound. No admitted theorem, custom axiom or native decision procedure is used.

Global 6840/2232 theorems remain unchecked. Both sharp universal 8/7 results and the stronger infinite all-prefix bound remain checked and unaffected.
