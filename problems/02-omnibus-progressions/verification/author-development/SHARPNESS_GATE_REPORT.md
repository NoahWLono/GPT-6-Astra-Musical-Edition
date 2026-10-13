# Sharpness gate: 2026-10-13 19:36–19:38 UTC

## Checked result

Both universal upper bounds are now formally attained in the explicitly defined descending-only model. SharpBounds.lean successfully checked actual finite and infinite ordered-chord walks. The infinite witness is not merely a quotient diagram: it has a proved admissible move at EVERY natural-number index, using a concrete 36-chord loop after one entrance chord.

The following exact exports are checked:

```lean
theorem eight_type_bound_is_attained :
    ∃ c : Nat → Chord, chord (c 0) = true ∧
      (∀ k < 7, OmnibusStep (c k) (c (k+1))) ∧
      ((Finset.range 8).image (fun n => sonority (c n))).card = 8

theorem infinite_witness_is_admissible :
    ∀ n, OmnibusStep (infiniteWitness n) (infiniteWitness (n+1))

theorem seven_prefix_bound_is_attained :
    ∃ c : Nat → Chord, (∀ n, OmnibusStep (c n) (c (n+1))) ∧
      ((Finset.range 7).image (fun n => sonority (c n))).card = 7 ∧
      sonority (c 7) = sonority (c 1)
```

The attainment theorems use exactly propext, Classical.choice and Quot.sound. The universal admissibility theorem uses propext and Quot.sound. There is no admitted proof, custom axiom, native-decision oracle, or assumed graph edge. Combined with the checked universal upper bounds, these establish exact sharp bounds 8 and 7.

SharpBounds source SHA-256: `557179c6a90ac995240933e37e6edc6b280e20345883d04ff81bbc7f1a3c0a32`.

SharpBounds olean SHA-256: `41b642db32c2e56f508b1f5215a1dccc10d8a832ef7b109c4ac4b6fb2a325eb2`.

## Additional checked count prerequisites

CountTranslation passed. Omnibus.step_back and back_step prove actual inverses for each move on bounded chords. image_membership identifies inImage with existence of a permitted ordered source chord under an actual move. image_translation proves transposition invariance. All four printed exports use only propext, Classical.choice and Quot.sound. These are semantic prerequisites, not cardinality results.

BassCountBijection subsequently hit the CPU watchdog and is NOT checked. The gate stopped immediately and slot 2 was released.

## Resources and every attempt

Aggregate actual child CPU including every failure: **30.974 seconds** of 60 authorized. Peak RSS: **1930636 KiB**, from the capped bijection attempt; successful SharpBounds peak RSS was 1656260 KiB. Unchanged -j1, 19.5-second CPU watchdog, hard 20 CPU seconds, 35 wall seconds, 2-GiB RSS, 64-MiB file and 4-GiB free-disk limits.

- PeriodicWitness, 2026-10-13T19:36:45.720967+00:00: exit 0; CPU 3.404s; wall 3.449s; RSS 828332 KiB; watchdog False.
  Source `df1ac7402e32f143d6531c3d2bfb4a2644dd71d2f707084c138ec1ec4ef83110`; olean `39b9d6d066beec6eec19ab400e394bf59662e50cc367609217cc278cad4c54d8`.
- SharpBounds, 2026-10-13T19:36:55.194223+00:00: exit 1; CPU 1.848s; wall 1.884s; RSS 1647908 KiB; watchdog False.
  Source `1b0ca586372c21515607e39c0b18bf16f101bb72cc6ed744b8752d69227614d8`; olean `None`.
- SharpBounds, 2026-10-13T19:37:06.592843+00:00: exit 0; CPU 2.132s; wall 2.184s; RSS 1656260 KiB; watchdog False.
  Source `557179c6a90ac995240933e37e6edc6b280e20345883d04ff81bbc7f1a3c0a32`; olean `41b642db32c2e56f508b1f5215a1dccc10d8a832ef7b109c4ac4b6fb2a325eb2`.
- CountTranslation, 2026-10-13T19:37:26.145709+00:00: exit 1; CPU 2.426s; wall 2.378s; RSS 764980 KiB; watchdog False.
  Source `b10801951254e35d271244f636fc179809e3cc32329ff222f6d38756b47e1da9`; olean `None`.
- CountTranslation, 2026-10-13T19:37:42.625900+00:00: exit 0; CPU 1.574s; wall 1.617s; RSS 779356 KiB; watchdog False.
  Source `4935b47ad03a59e020545efcd1a487c372b7aa48351741973d1f176ccca498ff`; olean `dd252e9f6a601b355285374416c35286c29a1ffd9bcaef15d46cd41c2fd73f9b`.
- BassCountBijection, 2026-10-13T19:37:47.904706+00:00: exit -9; CPU 19.590s; wall 19.601s; RSS 1930636 KiB; watchdog True.
  Source `d28164a6af2faa92664ff3db2b80742c01509c737e6afb9123bfe0bbcd11c92c`; olean `None`.

All attempt sources/logs/receipts are preserved under sharp_gate and hashed with successful artifacts in SHA256SUMS.sharp-gate. Historical SOURCE ONLY / NOT COMPILED comments in successful compiled source headers are superseded by the receipts and this report. Those headers were left byte-for-byte unchanged to preserve successful source hashes; clean header edits should be included in the next bounded independent replay. They must not be copied as present-tense verification claims into the paper.

## Scope and remaining work

Pyle's undefined extension/sonority terminology is not resolved by these theorems. The verified equivalence is bass-relative upper-multiset equality; only descending-bass moves are mixed within a walk. Mirror-only reversal has the corresponding ordinary mathematical statement. Mixed ascending/descending moves are excluded.

Image counts 6840/2232 and the lower-three return theorem remain unverified in Lean. Novelty is unestablished. Before publication, perform an independent clean rebuild and a separate prior-art/scope review.
