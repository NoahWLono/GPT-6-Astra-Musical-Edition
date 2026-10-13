import GoldenThreshold
import Mathlib.Data.Nat.Sqrt

/-! Checked formalization; see exact replay receipts. Executable threshold index for each integer bound. -/
namespace AlgebraicTunings

def goldenThresholdIndex (B : ℕ) : ℤ :=
  (Nat.sqrt ((4 * B + 3) / 5) : ℤ)

theorem goldenThresholdIndex_nonneg (B : ℕ) : 0 ≤ goldenThresholdIndex B := by
  unfold goldenThresholdIndex
  exact Int.natCast_nonneg _

theorem goldenThresholdIndex_depth (B : ℕ) :
    (5 * goldenThresholdIndex B * goldenThresholdIndex B) / 4 ≤ (B : ℤ) := by
  let m := Nat.sqrt ((4 * B + 3) / 5)
  have hs : m * m ≤ (4 * B + 3) / 5 := Nat.sqrt_le _
  have hb : 5 * (m * m) ≤ 4 * B + 3 := by omega
  have hbZ : 5 * ((m : ℤ) * m) ≤ 4 * (B : ℤ) + 3 := by exact_mod_cast hb
  change (5 * (m : ℤ) * m) / 4 ≤ (B : ℤ)
  rw [mul_assoc]
  omega

theorem goldenThresholdIndex_next (B : ℕ) :
    (B : ℤ) < (5 * (goldenThresholdIndex B + 1) *
      (goldenThresholdIndex B + 1)) / 4 := by
  let m := Nat.sqrt ((4 * B + 3) / 5)
  have hs : (4 * B + 3) / 5 < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
  have hb : 4 * B + 3 < 5 * ((m + 1) * (m + 1)) := by omega
  have hbZ : 4 * (B : ℤ) + 3 < 5 * (((m : ℤ) + 1) * ((m : ℤ) + 1)) := by
    exact_mod_cast hb
  change (B : ℤ) < (5 * ((m : ℤ) + 1) * ((m : ℤ) + 1)) / 4
  rw [mul_assoc]
  omega

#check @goldenThresholdIndex_depth
#check @goldenThresholdIndex_next
#print axioms goldenThresholdIndex_nonneg
#print axioms goldenThresholdIndex_depth
#print axioms goldenThresholdIndex_next
end AlgebraicTunings
