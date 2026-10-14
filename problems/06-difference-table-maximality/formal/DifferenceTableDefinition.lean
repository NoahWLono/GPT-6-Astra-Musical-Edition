import PositiveCircuitCertificate

namespace DifferenceTableResearch

abbrev QRow := Fin 9 → ℚ
abbrev QPoint := Fin 9 → ℝ
abbrev QConstraint := Bool × List QRow

def qEval (r : QRow) (z : QPoint) : ℝ := evalRow (fun i => (r i : ℝ)) z

def qUnit (i : ℕ) : QRow := fun j => if j.val = i then 1 else 0

def qSub (a b : QRow) : QRow := fun i => a i - b i

def qAdd (a b : QRow) : QRow := fun i => a i + b i

def qScale (a : ℚ) (b : QRow) : QRow := fun i => a * b i

def coord (target : Bool) (i : ℕ) : QRow :=
  if i = 0 then fun _ => 0 else qUnit (i + if target then 4 else 0)

def edgeEnds : Fin 10 → ℕ × ℕ :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def isLong (p : ℕ) (e : Fin 10) : Bool :=
  if p = 0 then false else if p = 1 then e.val == 3 else e.val == 2 || e.val == 3

def shortForm (p : ℕ) (target : Bool) (e : Fin 10) : QRow :=
  let d := qSub (coord target (edgeEnds e).2) (coord target (edgeEnds e).1)
  if isLong p e then qSub (qUnit 0) d else d

def matchingRows (p q : ℕ) (π : Fin 10 → Fin 10) : Fin 10 → QRow :=
  fun e => qSub (shortForm q true e) (shortForm p false (π e))

def canonicalConstraints (p : ℕ) (target : Bool) : List QConstraint :=
  let v := coord target
  let h := qScale (1/2) (qUnit 0)
  let gaps := (List.range 4).map (fun i => (true, [qSub (v (i+1)) (v i)]))
  let upper := [(true, [qSub (qUnit 0) (v 4)])]
  let longs := if p = 0 then [(false, [qSub h (v 4)])]
    else if p = 1 then [(true, [qSub (v 4) h]), (false, [qSub h (v 3)]),
      (false, [qAdd (qSub h (v 4)) (v 1)])]
    else [(true, [qSub (v 3) h]), (true, [qSub h (v 2)]),
      (false, [qAdd (qSub h (v 4)) (v 1)])]
  let reflection := if p < 2 then
    [(false, [qSub (qSub (v 4) (v 3)) (v 1),
      qAdd (qSub (v 3) (qScale 2 (v 2))) (v 1)])]
    else [(false, [qSub (qSub (qUnit 0) (v 4)) (v 1),
      qAdd (qSub (qSub (v 4) (v 3)) (v 2)) (v 1)])]
  gaps ++ upper ++ longs ++ reflection

def originalConstraints (p q : ℕ) : List QConstraint :=
  [(true, [qUnit 0])] ++ canonicalConstraints p false ++ canonicalConstraints q true ++
    (if p = q then [(true, (List.range 4).map
      (fun i => qSub (coord true (i+1)) (coord false (i+1))))] else [])

def TableHolds (p q : ℕ) (π : Fin 10 → Fin 10) (z : QPoint) : Prop :=
  z 0 = 1 ∧ (∀ e, qEval (matchingRows p q π e) z = 0) ∧
    ∀ c ∈ originalConstraints p q, LexSatisfied c.1 (c.2.map (fun r => qEval r z))

end DifferenceTableResearch

namespace DifferenceTableResearch

def qDot (r w : QRow) : ℚ := ∑ i, r i * w i

def QLexSatisfied (strict : Bool) : List ℚ → Prop
  | [] => strict = false
  | a :: tail => 0 < a ∨ a = 0 ∧ QLexSatisfied strict tail

def RationalTableHolds (p q : ℕ) (π : Fin 10 → Fin 10) (w : QRow) : Prop :=
  w 0 = 1 ∧ (∀ e, qDot (matchingRows p q π e) w = 0) ∧
    ∀ c ∈ originalConstraints p q, QLexSatisfied c.1 (c.2.map (fun r => qDot r w))

theorem qEval_cast (r w : QRow) :
    qEval r (fun i => (w i : ℝ)) = (qDot r w : ℝ) := by
  simp [qEval, qDot, evalRow]

theorem lex_cast_iff (strict : Bool) (l : List ℚ) :
    LexSatisfied strict (l.map (fun (x : ℚ) => (x : ℝ))) ↔ QLexSatisfied strict l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [LexSatisfied, QLexSatisfied, ih]

theorem rational_table_sound (p q : ℕ) (π : Fin 10 → Fin 10) (w : QRow)
    (h : RationalTableHolds p q π w) : TableHolds p q π (fun i => (w i : ℝ)) := by
  rcases h with ⟨h0, hr, hc⟩
  refine ⟨?_, ?_, ?_⟩
  · change (w 0 : ℝ) = 1
    exact_mod_cast h0
  · intro e
    rw [qEval_cast]
    exact_mod_cast hr e
  · intro c hm
    have hlex := (lex_cast_iff c.1 (c.2.map (fun r => qDot r w))).mpr (hc c hm)
    rw [List.map_map] at hlex
    change LexSatisfied c.1 (c.2.map (fun r => (qDot r w : ℝ))) at hlex
    simpa only [qEval_cast] using hlex

theorem qEval_unit (j : Fin 9) (z : QPoint) : qEval (qUnit j.val) z = z j := by
  have forms : (fun i => (qUnit j.val i : ℝ)) = (fun i => if i = j then 1 else 0) := by
    funext i
    by_cases h : i = j
    · subst i; simp [qUnit]
    · have hv : i.val ≠ j.val := fun hv => h (Fin.ext hv)
      simp [qUnit, h, hv]
  rw [qEval, forms]
  simp [evalRow]

theorem qEval_sub (a b : QRow) (z : QPoint) :
    qEval (qSub a b) z = qEval a z - qEval b z := by
  simp [qEval, evalRow, qSub, sub_mul, Finset.sum_sub_distrib]

theorem qEval_scale (a : ℚ) (r : QRow) (z : QPoint) :
    qEval (qScale a r) z = (a : ℝ) * qEval r z := by
  simp [qEval, evalRow, qScale, mul_assoc, Finset.mul_sum]

end DifferenceTableResearch

namespace DifferenceTableResearch
instance qLexDecidable (s : Bool) (l : List ℚ) : Decidable (QLexSatisfied s l) := by
  induction l with
  | nil => unfold QLexSatisfied; infer_instance
  | cons a l ih =>
    unfold QLexSatisfied
    haveI := ih
    infer_instance
instance rationalTableDecidable (p q : ℕ) (π : Fin 10 → Fin 10) (w : QRow) :
    Decidable (RationalTableHolds p q π w) := by
  unfold RationalTableHolds
  infer_instance
end DifferenceTableResearch

namespace DifferenceTableResearch

def augmentedRows {m : ℕ} (rows : Fin m → QRow) : Fin (m+1) → QRow :=
  Fin.lastCases (qUnit 0) rows

theorem qEval_right_sub (r : QRow) (z w : QPoint) :
    qEval r (fun i => z i - w i) = qEval r z - qEval r w := by
  simp [qEval, evalRow, mul_sub, Finset.sum_sub_distrib]

theorem augmented_difference_kernel {m : ℕ} (rows : Fin m → QRow) (z w : QPoint)
    (hz0 : z 0 = 1) (hw0 : w 0 = 1)
    (hz : ∀ i, qEval (rows i) z = 0) (hw : ∀ i, qEval (rows i) w = 0) :
    ∀ i, qEval (augmentedRows rows i) (fun j => z j - w j) = 0 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [augmentedRows, Fin.lastCases_last]
    change qEval (qUnit 0) (fun j => z j - w j) = 0
    have uz : qEval (qUnit 0) z = z 0 := by simpa using qEval_unit (0 : Fin 9) z
    have uw : qEval (qUnit 0) w = w 0 := by simpa using qEval_unit (0 : Fin 9) w
    rw [qEval_right_sub, uz, uw, hz0, hw0, sub_self]
  · simp only [augmentedRows, Fin.lastCases_castSucc]
    change qEval (rows j) (fun k => z k - w k) = 0
    rw [qEval_right_sub, hz j, hw j, sub_self]

end DifferenceTableResearch
