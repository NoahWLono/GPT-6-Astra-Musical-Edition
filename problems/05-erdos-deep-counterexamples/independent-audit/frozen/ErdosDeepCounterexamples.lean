import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
Direct finite counterexamples to the list of length triples in Dukes–Gaede (2023),
Conjecture 1, using the constituent admissibility convention of Gaede (2022), §2.2.
The computation counts unordered pairs in the actual lists of modular points.
All finite checks use kernel reduction (`decide`), not `native_decide`.
-/
namespace ErdosDeepTriples

/-- The standard cyclic distance, for representatives in `[0,n)`. -/
def cyclicDistance (n x y : Nat) : Nat :=
  min ((x + n - y) % n) ((y + n - x) % n)

/-- Actual representatives of the modular arithmetic progression. -/
def apPoints (n g k : Nat) : List Nat :=
  (List.range k).map (fun j => (j * g) % n)

/-- Every unordered pair of positions appears once, with the earlier position first. -/
def pairDistances (n : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => xs.map (cyclicDistance n x) ++ pairDistances n xs

def familyDistances (n : Nat) (gs ks : List Nat) : List Nat :=
  (gs.zip ks).flatMap (fun (g, k) => pairDistances n (apPoints n g k))

/-- Multiplicity at each possible positive cyclic distance. -/
def distanceMultiplicities (n : Nat) (gs ks : List Nat) : List Nat :=
  (List.range' 1 (n / 2)).map
    (fun d => (familyDistances n gs ks).count d)

/-- The nonzero multiplicities are exactly `1,...,K-1`, each once. -/
def IsErdosDeep (n : Nat) (gs ks : List Nat) (K : Nat) : Prop :=
  ((distanceMultiplicities n gs ks).filter (fun m => m != 0)).insertionSort (· ≤ ·) =
    List.range' 1 (K - 1)

/-- Half-order condition allowing all the constituent distances to remain distinct. -/
def Admissible (n g k : Nat) : Prop :=
  3 ≤ k ∧ 2 * (k - 1) ≤ n / Nat.gcd n g

def Primitive (n : Nat) (gs : List Nat) : Prop :=
  gs.foldl Nat.gcd n = 1

/-- The fifteen length triples stated in the published conjecture. -/
def claimedLengths : List (List Nat) :=
  [[4,4,3], [6,3,3], [6,5,3], [6,6,4], [6,6,6], [7,7,3], [9,4,3],
   [8,7,4], [8,8,5], [10,6,4], [12,4,4], [13,5,3], [13,7,4],
   [16,5,4], [21,6,4]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first_counterexample :
    Primitive 34 [1,6,12] ∧
    Admissible 34 1 10 ∧ Admissible 34 6 9 ∧ Admissible 34 12 5 ∧
    (apPoints 34 1 10).Nodup ∧ (apPoints 34 6 9).Nodup ∧
    (apPoints 34 12 5).Nodup ∧
    IsErdosDeep 34 [1,6,12] [10,9,5] 14 ∧
    [10,9,5] ∉ claimedLengths := by
  unfold Primitive Admissible IsErdosDeep
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem second_counterexample :
    Primitive 48 [1,6,18] ∧
    Admissible 48 1 20 ∧ Admissible 48 6 5 ∧ Admissible 48 18 5 ∧
    (apPoints 48 1 20).Nodup ∧ (apPoints 48 6 5).Nodup ∧
    (apPoints 48 18 5).Nodup ∧
    IsErdosDeep 48 [1,6,18] [20,5,5] 21 ∧
    [20,5,5] ∉ claimedLengths := by
  unfold Primitive Admissible IsErdosDeep
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first_histogram :
    distanceMultiplicities 34 [1,6,12] [10,9,5] =
      [9,13,7,10,5,12,3,4,1,8,0,11,0,2,0,6,0] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem second_histogram :
    distanceMultiplicities 48 [1,6,18] [20,5,5] =
      [19,18,17,16,15,20,13,12,11,10,9,14,7,6,5,4,3,8,1,0,0,0,0,2] := by decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first_constituents_deep :
    IsErdosDeep 34 [1] [10] 10 ∧
    IsErdosDeep 34 [6] [9] 9 ∧
    IsErdosDeep 34 [12] [5] 5 := by
  unfold IsErdosDeep
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem second_constituents_deep :
    IsErdosDeep 48 [1] [20] 20 ∧
    IsErdosDeep 48 [6] [5] 5 ∧
    IsErdosDeep 48 [18] [5] 5 := by
  unfold IsErdosDeep
  decide

/-- Both examples use the extra endpoint allowed in the thesis's §2.2,
    so neither refutes the strictly smaller search convention. -/
theorem endpoint_audit :
    9 = (34 / Nat.gcd 34 6) / 2 + 1 ∧
    5 = (48 / Nat.gcd 48 6) / 2 + 1 ∧
    5 = (48 / Nat.gcd 48 18) / 2 + 1 := by decide

/-- A precise, stronger-than-literal version of the proposed necessity statement:
    primitive family; ordered lengths >=3; distinct AP points; every constituent
    separately Erdős-deep; and the allowed half-order upper bounds. -/
def NormalizedClassification : Prop :=
  ∀ n g₁ g₂ g₃ k₁ k₂ k₃ K : Nat,
    0 < n → k₃ ≤ k₂ → k₂ ≤ k₁ →
    Primitive n [g₁,g₂,g₃] →
    Admissible n g₁ k₁ → Admissible n g₂ k₂ → Admissible n g₃ k₃ →
    (apPoints n g₁ k₁).Nodup → (apPoints n g₂ k₂).Nodup →
    (apPoints n g₃ k₃).Nodup →
    IsErdosDeep n [g₁] [k₁] k₁ →
    IsErdosDeep n [g₂] [k₂] k₂ →
    IsErdosDeep n [g₃] [k₃] k₃ →
    IsErdosDeep n [g₁,g₂,g₃] [k₁,k₂,k₃] K →
    [k₁,k₂,k₃] ∈ claimedLengths

theorem not_normalizedClassification : ¬ NormalizedClassification := by
  intro h
  rcases first_counterexample with ⟨hp,ha,hb,hc,hna,hnb,hnc,hd,hexcl⟩
  rcases first_constituents_deep with ⟨hda,hdb,hdc⟩
  exact hexcl (h 34 1 6 12 10 9 5 14 (by decide) (by decide) (by decide)
    hp ha hb hc hna hnb hnc hda hdb hdc hd)

#print axioms first_counterexample
#print axioms second_counterexample
#print axioms first_histogram
#print axioms second_histogram
#print axioms first_constituents_deep
#print axioms second_constituents_deep
#print axioms endpoint_audit
#print axioms not_normalizedClassification
end ErdosDeepTriples
