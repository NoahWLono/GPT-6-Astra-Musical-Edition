import IntegerSquares
import TilingBridge
import QueensBridge

namespace Rhythmic

/-- Quantitative bound for the actual transverse triples of a perfect rhythmic
triplet tiling. This is a supporting obstruction, not an existence theorem. -/
theorem PerfectTripletTiling.transverse_bound {k : ℕ} (T : PerfectTripletTiling k) :
    (T.transverseIndices.card : ℝ)^2 - 1 ≤
      3*(k : ℝ)*((k : ℝ)-T.transverseIndices.card) := by
  exact T.transverse_bound_of (@partial_transverse_bound)

/-- The same bound for any set of mutually nonattacking queens restricted to one
checkerboard color. Both colors are covered by the common-remainder hypothesis. -/
theorem monochromatic_queens_bound {k t : ℕ} (a c : Fin t → ℤ)
    (ha : Function.Injective a) (hc : Function.Injective c)
    (hsum : Function.Injective (fun i => a i + c i))
    (hdiff : Function.Injective (fun i => a i - c i))
    (hparity : ∃ p : ℤ, ∀ i, (a i + c i) % 2 = p)
    (ha0 : ∀ i, 0 ≤ a i) (hak : ∀ i, a i < k)
    (hc0 : ∀ i, 0 ≤ c i) (hck : ∀ i, c i < k) :
    (t : ℝ)^2 - 1 ≤ 3*(k : ℝ)*((k : ℝ)-t) := by
  exact monochromatic_queens_bound_of (@partial_transverse_bound_shifted)
    a c ha hc hsum hdiff hparity ha0 hak hc0 hck

#print axioms PerfectTripletTiling.transverse_bound
#print axioms monochromatic_queens_bound
end Rhythmic
