import SampleCollisionCertificate
namespace DifferenceTableResearch.MaximalA1
def piMap : Fin 10 → Fin 10 := ![0, 4, 5, 6, 9, 8, 3, 7, 2, 1]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 3 → QRow := ![![1, (1/14), (2/7), (5/14), (1/2), (1/14), (3/14), (2/7), (4/7)],
  ![1, (1/14), (23/84), (31/84), (1/2), (1/14), (17/84), (25/84), (4/7)],
  ![1, (1/12), (25/84), (31/84), (1/2), (1/12), (3/14), (2/7), (7/12)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 0 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalA1
namespace DifferenceTableResearch.MaximalA2
def piMap : Fin 10 → Fin 10 := ![9, 7, 5, 2, 0, 1, 3, 4, 6, 8]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 3 → QRow := ![![1, (1/14), (1/7), (5/14), (1/2), (1/7), (3/14), (2/7), (9/14)],
  ![1, (5/84), (13/84), (5/14), (1/2), (1/7), (17/84), (25/84), (9/14)],
  ![1, (5/84), (11/84), (29/84), (1/2), (13/84), (3/14), (2/7), (55/84)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 0 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalA2
namespace DifferenceTableResearch.MaximalD1
def piMap : Fin 10 → Fin 10 := ![8, 4, 1, 3, 7, 9, 6, 0, 2, 5]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (1/18), (5/18), (1/3), (4/9), (1/6), (2/9), (5/18), (5/9)],
  ![1, (1/27), (29/108), (1/3), (47/108), (1/6), (25/108), (29/108), (61/108)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 0 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalD1
namespace DifferenceTableResearch.MaximalD2
def piMap : Fin 10 → Fin 10 := ![8, 4, 1, 6, 9, 7, 3, 0, 2, 5]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (1/30), (4/15), (11/30), (13/30), (1/6), (7/30), (4/15), (3/5)],
  ![1, (1/24), (13/48), (3/8), (7/16), (1/6), (11/48), (13/48), (29/48)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 0 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalD2
namespace DifferenceTableResearch.MaximalD3
def piMap : Fin 10 → Fin 10 := ![1, 7, 8, 2, 0, 4, 3, 9, 6, 5]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (1/24), (1/6), (3/8), (11/24), (1/6), (5/24), (7/24), (5/8)],
  ![1, (7/192), (1/6), (71/192), (89/192), (1/6), (13/64), (19/64), (121/192)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 0 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalD3
namespace DifferenceTableResearch.MaximalF1
def piMap : Fin 10 → Fin 10 := ![0, 7, 5, 6, 1, 9, 3, 4, 8, 2]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (1/16), (1/8), (5/16), (1/2), (1/16), (3/16), (1/4), (9/16)],
  ![1, (5/64), (1/8), (21/64), (1/2), (5/64), (13/64), (1/4), (37/64)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 0 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalF1
namespace DifferenceTableResearch.MaximalF2
def piMap : Fin 10 → Fin 10 := ![8, 4, 5, 1, 0, 9, 3, 7, 6, 2]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (1/16), (5/16), (3/8), (1/2), (3/16), (1/4), (5/16), (11/16)],
  ![1, (3/64), (19/64), (3/8), (1/2), (13/64), (1/4), (21/64), (45/64)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 0 1 pi z → TableHolds 0 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 0 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalF2
namespace DifferenceTableResearch.MaximalA3
def piMap : Fin 10 → Fin 10 := ![4, 1, 2, 8, 0, 9, 6, 7, 3, 5]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 3 → QRow := ![![1, (1/10), (3/10), (2/5), (3/5), (1/5), (3/10), (2/5), (7/10)],
  ![1, (2/15), (1/3), (5/12), (19/30), (1/5), (1/3), (5/12), (7/10)],
  ![1, (1/12), (3/10), (2/5), (7/12), (13/60), (3/10), (2/5), (43/60)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 1 1 pi z → TableHolds 1 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 1 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalA3
namespace DifferenceTableResearch.MaximalF3
def piMap : Fin 10 → Fin 10 := ![9, 7, 2, 5, 0, 8, 6, 1, 3, 4]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (1/16), (1/4), (7/16), (9/16), (1/8), (3/16), (7/16), (5/8)],
  ![1, (5/64), (1/4), (29/64), (37/64), (1/8), (13/64), (29/64), (5/8)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 1 1 pi z → TableHolds 1 1 σ z) → σ = pi := by
  apply sample_collision_free_maximal 1 1 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalF3
namespace DifferenceTableResearch.MaximalD4
def piMap : Fin 10 → Fin 10 := ![1, 2, 6, 8, 7, 9, 3, 5, 0, 4]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (2/9), (5/18), (7/18), (2/3), (5/18), (7/18), (5/9), (11/18)],
  ![1, (11/48), (7/24), (19/48), (2/3), (7/24), (19/48), (9/16), (5/8)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 1 2 pi z → TableHolds 1 2 σ z) → σ = pi := by
  apply sample_collision_free_maximal 1 2 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalD4
namespace DifferenceTableResearch.MaximalF4
def piMap : Fin 10 → Fin 10 := ![4, 7, 2, 8, 9, 3, 6, 1, 5, 0]
noncomputable def pi : Fin 10 ≃ Fin 10 := Equiv.ofBijective piMap (by decide +kernel)
def samples : Fin 2 → QRow := ![![1, (1/8), (5/16), (9/16), (5/8), (3/16), (1/4), (9/16), (11/16)],
  ![1, (1/8), (21/64), (37/64), (5/8), (13/64), (1/4), (37/64), (45/64)]]
theorem globally_maximal : ∀ σ : Fin 10 ≃ Fin 10,
    (∀ z, TableHolds 2 2 pi z → TableHolds 2 2 σ z) → σ = pi := by
  apply sample_collision_free_maximal 2 2 pi samples
  · decide +kernel
  · decide +kernel
#print axioms globally_maximal
end DifferenceTableResearch.MaximalF4
