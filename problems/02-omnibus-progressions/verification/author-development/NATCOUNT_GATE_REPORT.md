# Natural-cardinality count gate: 2026-10-13 20:01–20:04 UTC

The semantic/cardinality chain passed: BassNatCardinality, ImageCountDefinitions, ImageEnumerationSemantics, DisjointSliceCardinality, ImageSliceSemantics and ActualChordCardinality. Thus the true factor-12 bijection, raw generator equality with actual sources/images, exact disjoint-slice sum and encoded-to-actual image-set conversion are checked. Printed nontrivial semantic/cardinality exports use only propext, Classical.choice and Quot.sound (actualChordPredicateEquiv uses only propext).

Numerical tenor slices 0–3 passed. Their source counts are axiom-free; image/approachable counts use propext. Slice 4 hit the CPU watchdog before a successful artifact, so no result is accepted from it. The gate stopped and released slot 2. Subsequent finer partition work belongs to the separately authorized cellcount_gate.

Aggregate actual child CPU: **62.903 seconds**, all failures included, of 120 authorized. Peak RSS **1931912 KiB**. Every compiler had unchanged resource limits.

## Every attempt

- BassNatCardinality, 2026-10-13T20:01:42.624316+00:00: exit 0; CPU 2.069s; wall 2.093s; RSS 1834388 KiB; CPU stop False.
  Source `79c3c8847255b9f12e7ec18868d21a2cf2d72aee31164fae2fb237d729089c13`; olean `d3176e98f1a0c299707a7ea3e0fd9965e353411095e5b79b158e042a4e7bea1b`.
- ImageCountDefinitions, 2026-10-13T20:01:59.879155+00:00: exit 0; CPU 2.537s; wall 2.576s; RSS 1571404 KiB; CPU stop False.
  Source `27c7b243df6cbb6235dc6a9c46fff2fab6bbbc3cfd834a9bb4367fac9d41862d`; olean `89c7fae182dbf3e3401a13947755a6d73315fc2b0129e9e8e0eda0d6da3a87a3`.
- ImageEnumerationSemantics, 2026-10-13T20:02:02.578993+00:00: exit 0; CPU 4.857s; wall 4.912s; RSS 1578784 KiB; CPU stop False.
  Source `9da62742f1af33093670f91624a520bbb3a1ea22ad26784356cdae7d854155e3`; olean `602f227d14b2ccbf757560b5e9eaf5bc70f65ef4011af9ffe94d27664429460d`.
- DisjointSliceCardinality, 2026-10-13T20:02:14.616475+00:00: exit 1; CPU 2.124s; wall 2.132s; RSS 1829804 KiB; CPU stop False.
  Source `663a30101330040873f1df286f3273066c40f7ae0623c00a6f82a77ff75f32de`; olean `None`.
- DisjointSliceCardinality, 2026-10-13T20:02:40.215744+00:00: exit 0; CPU 1.704s; wall 1.728s; RSS 1842060 KiB; CPU stop False.
  Source `16c2715ff1642bad99e64617db7315762fd946e822b6e25e59462bc7a734cd69`; olean `24a79130bf75a34c6685a01a338870d263d2a9fd230fbc70cf3ff7269719540e`.
- ImageSliceSemantics, 2026-10-13T20:02:42.058676+00:00: exit 0; CPU 1.642s; wall 1.678s; RSS 1837036 KiB; CPU stop False.
  Source `de58ad1c2cafe6854641006a231d67e587ed033f72bab4a9fe24c6b4247cc68a`; olean `0571939c817f490e8e0dc30cffa705332b7dc4b3c626842e6034bbe6cd26884c`.
- ActualChordCardinality, 2026-10-13T20:02:43.836588+00:00: exit 0; CPU 1.781s; wall 1.785s; RSS 1840344 KiB; CPU stop False.
  Source `6e7abdf81d030fc695069fa34d9d996da518c89555a517ec98733d26f7ebfe8a`; olean `762a035b66ad8b3d61a65c6b3c912af84065c4861d4b97ceac3f82f9bab36553`.
- ImageCountSlice0, 2026-10-13T20:03:00.834611+00:00: exit 0; CPU 4.177s; wall 4.213s; RSS 1655764 KiB; CPU stop False.
  Source `7cb044fa495b6946257c63a2ccf3f13b7e04c7f720b6217a1ea66339f34a3367`; olean `72ec95f030db5ae21605232a458db75b0c11d2993f89b770e5e102e6a02f9ff5`.
- ImageCountSlice1, 2026-10-13T20:03:22.963776+00:00: exit 0; CPU 9.158s; wall 9.196s; RSS 1824412 KiB; CPU stop False.
  Source `69bc5dc888f2878c2dcea41c143272c6de41f0d1e1ce53d6c3eeaca321063801`; olean `035f64ec2a7953a959df4e9cf6725d2bf5c739ebd986bfddb3f5f832f4a128df`.
- ImageCountSlice2, 2026-10-13T20:03:32.288174+00:00: exit 0; CPU 6.199s; wall 6.243s; RSS 1751208 KiB; CPU stop False.
  Source `698f11454469cc05f3efb586f43b3fc1a99d92d7fa285faef778f0b0c23aae76`; olean `bb905998a0b02dbec6b067080bd98da21fea0e6bed13029f34a34965ef07c77f`.
- ImageCountSlice3, 2026-10-13T20:03:38.731514+00:00: exit 0; CPU 6.971s; wall 7.018s; RSS 1683720 KiB; CPU stop False.
  Source `6992a4b272c24b83b5aefdf4ceb72ca1584048aaf42a0f07256d8c911f487e7a`; olean `d496d481c6cad3c28504170686cd71dabc936504ece741fbd0ecf5a6872aa2bb`.
- ImageCountSlice4, 2026-10-13T20:03:45.963708+00:00: exit -9; CPU 19.684s; wall 19.720s; RSS 1931912 KiB; CPU stop True.
  Source `5e4fee1419ae530585e4d5b287d76777abd4f6f83cc0de4406a3c5831b0f49ff`; olean `None`.

Attempt inputs/logs/receipts are frozen in natcount_gate. The failed slice-4 original source is preserved there even though the current source file is subsequently replaced by a proved finer-partition assembly. No failed source is treated as checked. Numerical completion remains dependent on the separately audited fine slices and final theorem assembly.
