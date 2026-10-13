/- Six-note one-exchange homometry project.
Pinned toolchain: Lean 4.32.2, Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Proof bodies passed the main compile and axiom audit. These comment-normalized
sources are frozen for independent replay; see frozen_sources.json and the
separate independent verification receipt for the final replay status. -/
import AmbientBound
import SixExchangeDefinition

namespace OnePitchShift

theorem twelve_le_modulus_of_six_exchange (n : ℕ) [NeZero n]
    (h : SixExchange n) : 12 ≤ n := by
  obtain ⟨C, d, hc, hz, hd, hne, hh, hs⟩ := h
  have hsize := strict_exchange_ambient_bound C d hz hd hne hh hs
  rw [hc, ZMod.card] at hsize
  have horders := strict_six_note_exchange_orders C d hz hd hne hc hh hs
  have hdiv := six_note_modulus_necessary n C d hz hd hne hc hh hs
  by_contra hn
  have htwo : 2 ≤ addOrderOf d := by omega
  have hnine : n = 9 := by
    rcases hdiv with ⟨k, hk⟩ | ⟨k, hk⟩ <;> omega
  have hord : addOrderOf d = 2 := by omega
  have heven : Even (addOrderOf d) := by rw [hord]; decide
  have href := twice_exchange_order_dvd_modulus n C d hz hd hh
    (by rw [hc]; decide) heven
  rw [hord] at href
  obtain ⟨k, hk⟩ := href
  omega

end OnePitchShift
