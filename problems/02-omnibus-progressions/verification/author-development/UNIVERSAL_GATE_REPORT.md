# Universal bound gate: 2026-10-13 19:27–19:30 UTC

## Result

The concrete universal eight-type finite-walk upper bound and seven-type infinite-prefix upper bound are now checked in Lean 4.32.2. No graph edge or node is assumed: the proof uses the literal chord/move definitions, checked intrinsic node slices and successor equations, universal normalization/projection, finite closed-set certificates, and generic cardinality/pigeonhole lemmas.

Slot 2 was released after success. Aggregate actual child CPU, including all failed attempts: **69.084 seconds** of 90 authorized. Peak RSS: **1653708 KiB**. No process hit its CPU/wall/RSS cap in this gate. A guarded tactic-heartbeat timeout failed quickly and was repaired; it counts in the total.

## Exact final statements

In namespace Omnibus, UniversalBounds.lean exports:

```lean
theorem universal_eight_type_bound (c : Nat → Chord) (n : Nat)
    (hc₀ : chord (c 0) = true)
    (hc : ∀ k < n, OmnibusStep (c k) (c (k+1))) :
    ((Finset.range (n+1)).image (fun k => sonority (c k))).card ≤ 8

theorem universal_seven_prefix_bound (c : Nat → Chord)
    (hc : ∀ k, OmnibusStep (c k) (c (k+1))) :
    ∃ i j : Nat, i < j ∧ j ≤ 7 ∧ sonority (c i) = sonority (c j)
```

Both axiom inventories are exactly `[propext, Classical.choice, Quot.sound]`. There is no sorryAx, native-decide axiom, custom axiom, assumed graph edge, or unverified arithmetic oracle. The finite theorem bounds all distinct visited types, not merely the length of a simple path. The infinite theorem establishes an upper bound on first repetition; it does not on its own establish sharpness or the lower-three return bound.

UniversalBounds source SHA-256: `60b35edbc2cd17b6f7651e917db808a119b2a964041e4fa2bfca65c72334acdb`.

UniversalBounds olean SHA-256: `69ac20f9301269d7d9e6dbbb2daea982dcb0cae6e385e107092cf10d17a12918`.

## Verified dependency chain

1. Pilot defines literal chord membership by all 24 reorderings and interval tests, three actual contrary-motion moves, and bass-relative sorted types. Its witness certificates were checked earlier.
2. TranslationBridge, CanonicalBridge and QuotientSymmetry establish translation, canonical chord membership, sorting and upper-voice symmetry.
3. ReachableTranslation, ReachablePermutations and ReachableCanonical establish invariance of actual reachable types. LocalQuotientLift proves exact successor membership from every valid representative. Its forward projection is used for the bounds.
4. NodeSlice0–11 classify all intrinsic sorted candidates. NodeJoin.nodes_exact joins them into the full 55-node list; NodeJoin.chord_type_in_nodes universally covers every valid ordered chord.
5. EdgeSlice0–6 prove all 55 actual successor equations (49 edges total in the supplied table; the numeric edge-count corollary itself was not separately exported).
6. ClosureSlice0–6 prove 55 certificates: each starting node belongs to its listed closed set, that set is closed under intrinsic successors, and it has at most seven nonterminal vertices. ClosedWalkBounds derives the finite and infinite cardinality statements for every walk in such a set.
7. UniversalBounds instantiates those generic results for all actual chord walks. No reverse/infinite-lifting theorem is needed for these upper bounds.

Axiom audit by group: node_slice_2–11 are axiom-free (as are previously checked node_slice_0–1); nodes_exact uses only propext; successor_0–54 and closure_certificate_0–54 use only propext; reachable_cases/swap/cycle use propext and Quot.sound; universal semantic/cardinality theorems use only the three standard axioms listed above. Exact printed output is preserved per module.

## Every attempt

- ReachableTranslation, 2026-10-13T19:27:08.298330+00:00: exit 0; CPU 0.587s; wall 0.609s; RSS 755844 KiB.
  Source SHA-256 `05ec01bf4e81376ea24afa11c31e104df4b9a86771ad68a8b67c4e8b93cfd4bf`; olean `5ef47e61a7717e7f0e7ccc6e4b0680f89def17ee14e554b6b2f44ecc690dfd24`.
- ReachablePermutations, 2026-10-13T19:27:17.231197+00:00: exit 1; CPU 0.744s; wall 0.769s; RSS 751576 KiB.
  Source SHA-256 `a8c18ddc79c7853fec5aa9ec7f2d0ca229cafc6ce8817c7ba91a86fc763ecd4a`; olean `None`.
- ReachablePermutations, 2026-10-13T19:27:28.212277+00:00: exit 0; CPU 1.415s; wall 1.426s; RSS 765184 KiB.
  Source SHA-256 `4ccbe2f8b8c76b774ca5e0c55220fe90e55fe275f143c622a3a50f12373a8b8d`; olean `06243e2f4f3d5d972c179594a0b59b6963dd36b4dd789313674fa5e13c02b5ab`.
- ReachableCanonical, 2026-10-13T19:27:29.816051+00:00: exit 1; CPU 4.092s; wall 4.100s; RSS 749472 KiB.
  Source SHA-256 `71ab7df1a164baf17c08e4a1b5dbc10a5cd3651103e29fa9b7998adfea7cf8b9`; olean `None`.
- ReachableCanonical, 2026-10-13T19:27:44.119547+00:00: exit 0; CPU 0.667s; wall 0.710s; RSS 758204 KiB.
  Source SHA-256 `0a585e1a7ffb708d0c3921970a91f81e4ba7bc982952c37cb0dc97c8a3d05b24`; olean `9d5e97b94a913225b750c969eb45df0750061eb924edf8b8f13e408a7d0173b2`.
- LocalQuotientLift, 2026-10-13T19:27:52.570458+00:00: exit 0; CPU 1.485s; wall 1.534s; RSS 760084 KiB.
  Source SHA-256 `18583feec05161bf0538c646806c0a788c80208c2931d59e7cfa03357e55c41a`; olean `a4e3efaa94b51882b6b7e97457388f5643b3634d102317881dbd669d51b3f7ea`.
- NodeSlice2, 2026-10-13T19:28:08.729476+00:00: exit 0; CPU 3.837s; wall 3.892s; RSS 876768 KiB.
  Source SHA-256 `bfbbd40b65e76b94a829db6b1d5d0cc5c6242f5c78204473b286844ff9bb5515`; olean `e96c78d461087dbd231b1ee25d2529847552c30c9e88352f96888190a25b32eb`.
- NodeSlice3, 2026-10-13T19:28:12.723058+00:00: exit 0; CPU 2.623s; wall 2.687s; RSS 838272 KiB.
  Source SHA-256 `ca9d66ce1ed06cca2daeaa4560d2bf0a554eb4e6aef87600963edf74b19e4ca7`; olean `97140696740fc2391839e93052c7d866853357d4057a5a7b74a70c36401b42b7`.
- NodeSlice4, 2026-10-13T19:28:15.531677+00:00: exit 0; CPU 2.087s; wall 2.128s; RSS 821832 KiB.
  Source SHA-256 `72558b16ba2ede1ac68bf3b8dc077d9d57f3e36d28b8bccc691036fa47ff2919`; olean `8d014cf45d6474aab31933bb4fb464d729a03735ff5ceaebfe3949a1f2f75cec`.
- NodeSlice5, 2026-10-13T19:28:17.759132+00:00: exit 0; CPU 1.881s; wall 1.922s; RSS 813712 KiB.
  Source SHA-256 `592d62968c485ce1d5dec3924439c18476ca66d27f5b1865e83448e966af9270`; olean `1db66ae769a43cf8b0d1a212c5a7e0955732cef84311e3c64c007b1ea0f9e9ec`.
- NodeSlice6, 2026-10-13T19:28:19.798215+00:00: exit 0; CPU 2.071s; wall 2.074s; RSS 798932 KiB.
  Source SHA-256 `1a707b3994c3e182e8ebec9f76d597d4e7753e3ae9ae27d2ccef540d2bc7f421`; olean `d3ea1b893db009c066bae95ef16e320898253f449cac4d3b63e0a82b2ee4a845`.
- NodeSlice7, 2026-10-13T19:28:21.985680+00:00: exit 0; CPU 1.371s; wall 1.417s; RSS 790532 KiB.
  Source SHA-256 `061ec15b9746fd07761624c6686f5b7051d3ea65851442bb744525f24bfce95a`; olean `11f4de3bb16e5f6748162c8e6399b14334aefc0fb6c0e944e9421b179b362fa3`.
- NodeSlice8, 2026-10-13T19:28:23.524531+00:00: exit 0; CPU 1.216s; wall 1.305s; RSS 776452 KiB.
  Source SHA-256 `6940bcb863670d867ee201efd6ad1f1f00abe4fac0b327b969456ba73be8bbf1`; olean `1d535487250f7441cee28a9a79a70a544ca7acc19380a25520a6821cb412ce69`.
- NodeSlice9, 2026-10-13T19:28:24.936802+00:00: exit 0; CPU 0.896s; wall 0.912s; RSS 766980 KiB.
  Source SHA-256 `45e773d1e62530e7dad3d03408b25b56e8be5487173e784ccbaa0f389ef6a8ba`; olean `61af4cc4ea0065062eebf224be6de820126f4d70fe27266250ed9f50d5601316`.
- NodeSlice10, 2026-10-13T19:28:25.960055+00:00: exit 0; CPU 0.745s; wall 0.762s; RSS 761792 KiB.
  Source SHA-256 `ca7379bfb289c535defcfa894e570d5bbc7a93e2c444e6137ca3167d0d25e5e0`; olean `3c47dc32a0e6530e1fc40f4f0385704efc89eb7e08bfedf5bc06dddbb02ac0d9`.
- NodeSlice11, 2026-10-13T19:28:26.816019+00:00: exit 0; CPU 0.861s; wall 0.914s; RSS 757764 KiB.
  Source SHA-256 `4307cf6fac8d239b4a3e93a0d1fb327d0e9c2c47f74e6fc72ad27fb510e93331`; olean `0b82c40aca90007649db625f9a749ebd7112a0b9a2176e2b2669efdbb9fefb56`.
- NodeJoin, 2026-10-13T19:28:31.233675+00:00: exit 1; CPU 5.892s; wall 5.944s; RSS 984540 KiB.
  Source SHA-256 `7f288ae3941c8d7c35d54abe465b33231907859c6a61665dbdbc1141bc9fea15`; olean `None`.
- NodeJoin, 2026-10-13T19:28:57.478636+00:00: exit 0; CPU 5.816s; wall 5.866s; RSS 986624 KiB.
  Source SHA-256 `66425aa08caac7528b48a906f55adba90689006c84658ff7a574d55dee8f4b62`; olean `0b79f57be128650f404c8651fb40d520452376c7b3174bc058fbec32ac4ca691`.
- EdgeSlice0, 2026-10-13T19:29:18.044693+00:00: exit 0; CPU 3.088s; wall 3.131s; RSS 758952 KiB.
  Source SHA-256 `a39b3bccca35fd142ab2c877e215ec3556f04d5d31152a9bba06b73f86a00740`; olean `9549e52188e7a3e9ddd11ef51bf5081b22f8778a6ff6ad8c22f84e8b12575bb7`.
- EdgeSlice1, 2026-10-13T19:29:21.283392+00:00: exit 0; CPU 3.444s; wall 3.462s; RSS 759228 KiB.
  Source SHA-256 `80db96270718ff3f01c22b3e3a8cd541dc2c5fdd651afbb5814f174313a55719`; olean `e7e92c298d068517e00c9dca5402a2400d0397c7ff97146bd8a7aa805b71c380`.
- EdgeSlice2, 2026-10-13T19:29:24.858296+00:00: exit 0; CPU 2.958s; wall 2.996s; RSS 759468 KiB.
  Source SHA-256 `a6438c950d7d76a1d5392eb7e82ed94b6267e13202a707d853b55f98864f63f8`; olean `da90903dc21098ae7e21836036ebb71c1178ac1a0b2b6c9c87f82702d5f47c4e`.
- EdgeSlice3, 2026-10-13T19:29:27.995197+00:00: exit 0; CPU 2.153s; wall 2.188s; RSS 760160 KiB.
  Source SHA-256 `2ccb566113437e9b7a55528ce039b71b28f5f0701a4fcf957b00b188397c9261`; olean `1f2692d60476a8f0d2b0ca4aec0c70ce48ee21ba558658b021d5e697c4011f5b`.
- EdgeSlice4, 2026-10-13T19:29:30.412137+00:00: exit 0; CPU 3.206s; wall 3.241s; RSS 760660 KiB.
  Source SHA-256 `514d1ebc7e919b97df9f4fb043dfdd36c1bbff3d99d3ede6c9fdf691770b8dac`; olean `dc78f992e2a0db5ffe6a9246166fb408f5e85d2d893fec50eebaa6e7075c29b9`.
- EdgeSlice5, 2026-10-13T19:29:33.810186+00:00: exit 0; CPU 2.269s; wall 2.287s; RSS 759732 KiB.
  Source SHA-256 `56c8bbf45ce815decb0d10b6ccf54345ee71c9abb0add3887c39b278cb83e4ca`; olean `f4d840ad76ddcf60c691408c21269ca9c9b93303b8890c822b692d30624f6796`.
- EdgeSlice6, 2026-10-13T19:29:36.245277+00:00: exit 0; CPU 2.144s; wall 2.178s; RSS 761072 KiB.
  Source SHA-256 `51c7439e44519f33ae5ef1ccd79aa4a5bff0f58704b6c91d8acfdf927d411553`; olean `8ba781ff969037529eaf69e6031c2c79e62814c7665da5a1d6d1d3f4103fe238`.
- ClosureDefinitions, 2026-10-13T19:29:45.788425+00:00: exit 0; CPU 0.555s; wall 0.609s; RSS 753148 KiB.
  Source SHA-256 `28eb04dec19b7140a7cfd46b8102ce629d3dc536e4733e816be97240a35bce24`; olean `d094b4f1c47658e55fa0efdcb43dd78828459970ee5de395c538954d29eef0a8`.
- ClosedWalkBounds, 2026-10-13T19:29:46.507644+00:00: exit 0; CPU 1.807s; wall 1.821s; RSS 1547480 KiB.
  Source SHA-256 `49d25b403fd3e9b9ba548765406d2a33abe7801a98edb30bf2d1161c5a830c25`; olean `de7d84461c9e233ac39d3dfee3e89681c5c13b958d63e8a28b75546e7ce7ca08`.
- ClosureSlice0, 2026-10-13T19:29:55.448846+00:00: exit 0; CPU 0.899s; wall 0.910s; RSS 763244 KiB.
  Source SHA-256 `aff6e9dda46b4ddb7a7c9100f0fc5a1817683d3a5ad952a76a6050c9df089ae3`; olean `16a78b22694ec21a7c010b9928a86ee7ea295fdca0d77fccf53271ff51753543`.
- ClosureSlice1, 2026-10-13T19:29:56.465607+00:00: exit 0; CPU 0.896s; wall 0.910s; RSS 760624 KiB.
  Source SHA-256 `3beb202a40cfa03b3063fb01bdbc415dfc122a3d6fc096b1d499f50e2ed5fd6f`; olean `142c91eb95d17476a92b02159aac5fe13a88d4dc82fb2ea2f12a9e7031128642`.
- ClosureSlice2, 2026-10-13T19:29:57.473306+00:00: exit 0; CPU 0.834s; wall 0.862s; RSS 763660 KiB.
  Source SHA-256 `cda6ff471f615ddde6702bdb8bae2af5fd2e4423aba797903fffaa84c09141c4`; olean `5e4596f5474333ac728d85f4e9c38b0690fefdb3bff07ca46697359e37556a79`.
- ClosureSlice3, 2026-10-13T19:29:58.425315+00:00: exit 0; CPU 1.032s; wall 1.062s; RSS 764456 KiB.
  Source SHA-256 `4348c80b8b3a5770ef9c0606d7559fe40c2e0e3168a70ab4caf4b67cda9d7cb0`; olean `11f2291512974de6157f282ef357c79679441aef491531597ee7af2f7d3fa50c`.
- ClosureSlice4, 2026-10-13T19:29:59.588945+00:00: exit 0; CPU 0.699s; wall 0.708s; RSS 762176 KiB.
  Source SHA-256 `6c26e79a1e3a0dd26092abcc4db4beca0d15df98998376ec34a5bdb6c504c65e`; olean `59745b5900d9fe134f0572dbd58b333677358457aa1afa928d366078f54f929a`.
- ClosureSlice5, 2026-10-13T19:30:00.430799+00:00: exit 0; CPU 0.834s; wall 0.864s; RSS 762672 KiB.
  Source SHA-256 `c6bc04da0772c6aac2dc5b708a85225f0c62e5fd51d1fa78b9ebd88fd8b9055e`; olean `b114986d8bdb5a3617b56ab57a739e41928b693cca5198c4d44e3e92ecfbccdf`.
- ClosureSlice6, 2026-10-13T19:30:01.389987+00:00: exit 0; CPU 0.746s; wall 0.762s; RSS 760340 KiB.
  Source SHA-256 `de9fc40d8170659dbb718c01f5d57e03c127d4932b25c536c7d89636ae7737f1`; olean `d54e0c0cc323748a9ad7600252185080c0b739753c2faef73610270dca568336`.
- ClosureCertificates, 2026-10-13T19:30:07.947760+00:00: exit 0; CPU 0.588s; wall 0.613s; RSS 748236 KiB.
  Source SHA-256 `f257935b87c9f119f085a5ba5836ddfc60173b20d88d1ec599e01105383ce49b`; olean `d600681a268171fe617f9e2a0b16412c35309449d136bae3340c8a18a39c2bf1`.
- UniversalBounds, 2026-10-13T19:30:08.670112+00:00: exit 0; CPU 2.646s; wall 2.685s; RSS 1653708 KiB.
  Source SHA-256 `60b35edbc2cd17b6f7651e917db808a119b2a964041e4fa2bfca65c72334acdb`; olean `69ac20f9301269d7d9e6dbbb2daea982dcb0cae6e385e107092cf10d17a12918`.

Each attempt has a frozen source, log and receipt in guarded_gate. Current successful sources/artifacts and all attempt data are hashed in SHA256SUMS.universal-gate. Source-only comments within successfully compiled source files are historical and superseded by these receipts; the exact compiled sources are frozen unchanged.

## Resource enforcement and libraries

Every compiler ran -j1 under the existing 19.5 CPU-second watchdog, 20-second hard CPU limit, 35 wall-second watchdog, 2-GiB RSS watchdog, 64-MiB output-file limit and checked 4-GiB free-space floor. The aggregate driver included all failures and would shrink the final process budget to remaining CPU minus its polling margin. No address-space limit was substituted for RSS.

ClosedWalkBounds imports existing Mathlib.Data.Finset.Card and Mathlib.Data.Finset.Range from Mathlib 4.32.2. The wrapper now adds only the read-only existing Mathlib and package olean directories to LEAN_PATH. No upstream library was changed or rebuilt.

## Still separate/unverified

- The actual infinite sharpness witness (seven distinct types before repetition), and formal lower-three return bound.
- Exact image cardinalities 6840 and 2232, including their transposition-bijection bridge.
- Novelty/priority, authorial interpretation of Conjecture 1, and the paper's undefined extension relation.
- An assembled sharp finite theorem is not yet exported, although its universal upper bound and the intrinsic eight-type witness components are individually checked.

The checked model is the explicitly stated descending-only, bass-relative upper-multiset model. No claim is made to settle the source paper's ambiguous Conjecture 1.
