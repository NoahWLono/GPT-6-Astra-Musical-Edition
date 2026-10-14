import SampleCollisionCertificate
import BlockMaximality

namespace DifferenceTableResearch

def nonnegativeHeads (p q : ℕ) : List QRow :=
  (fun _ => 0) :: (originalConstraints p q).map (fun c => c.2.headD (fun _ => 0))

theorem heads_nonnegative (p q : ℕ) (σ : Fin 10 → Fin 10) (z : QPoint)
    (h : TableHolds p q σ z) (f : QRow) (hf : f ∈ nonnegativeHeads p q) :
    0 ≤ qEval f z := by
  rcases List.mem_cons.mp hf with hf | hf
  · subst f
    simp [qEval, evalRow]
  · obtain ⟨c, hc, eqf⟩ := List.mem_map.mp hf
    have hl := h.2.2 c hc
    cases he : c.2 with
    | nil =>
      simp [he] at eqf
      subst f
      simp [qEval, evalRow]
    | cons a tail =>
      simp [he] at eqf
      subst f
      simp only [he, List.map_cons] at hl
      exact lex_head_nonnegative c.1 _ _ hl

def withPair (rows : Fin 10 → QRow) (f g : QRow) : Fin 12 → QRow :=
  ![rows 0, rows 1, rows 2, rows 3, rows 4, rows 5, rows 6, rows 7, rows 8, rows 9, f, g]

structure ReverseCertificate where
  f : QRow
  g : QRow
  weight : ℚ
  zeroCoeff : Fin 10 → ℚ
  recovery : Fin 10 → Fin 12 → ℚ

def ReverseCertificate.Valid (p q : ℕ) (π σ : Fin 10 → Fin 10)
    (c : ReverseCertificate) : Prop :=
  c.f ∈ nonnegativeHeads p q ∧ c.g ∈ nonnegativeHeads p q ∧ 0 < c.weight ∧
  (∀ k, c.f k + c.weight * c.g k = ∑ i, c.zeroCoeff i * matchingRows p q σ i k) ∧
  ∀ e k, matchingRows p q π e k = ∑ i, c.recovery e i *
    withPair (matchingRows p q σ) c.f c.g i k

instance (p q : ℕ) (π σ : Fin 10 → Fin 10) (c : ReverseCertificate) :
    Decidable (c.Valid p q π σ) := by unfold ReverseCertificate.Valid; infer_instance

theorem compact_reverse_sound (p q : ℕ) (π σ : Fin 10 → Fin 10)
    (c : ReverseCertificate) (valid : c.Valid p q π σ) :
    ∀ z, TableHolds p q σ z → TableHolds p q π z := by
  intro z hz
  obtain ⟨hf, hg, hw, zero, recover⟩ := valid
  have ident : (fun k => (1 : ℝ) * (c.f k : ℝ) + (c.weight : ℝ) * (c.g k : ℝ)) =
      fun k => ∑ i, (c.zeroCoeff i : ℝ) * (matchingRows p q σ i k : ℝ) := by
    funext k
    simp only [one_mul]
    exact_mod_cast zero k
  have pair := positive_pair_zero_certificate (fun i => (c.zeroCoeff i : ℝ))
    (fun i k => (matchingRows p q σ i k : ℝ)) z
    (fun k => (c.f k : ℝ)) (fun k => (c.g k : ℝ)) 1 (c.weight : ℝ)
    (by norm_num) (by exact_mod_cast hw)
    (heads_nonnegative p q σ z hz c.f hf) (heads_nonnegative p q σ z hz c.g hg)
    ident hz.2.1
  have hk : ∀ i, qEval (withPair (matchingRows p q σ) c.f c.g i) z = 0 := by
    intro i
    fin_cases i
    · exact hz.2.1 0
    · exact hz.2.1 1
    · exact hz.2.1 2
    · exact hz.2.1 3
    · exact hz.2.1 4
    · exact hz.2.1 5
    · exact hz.2.1 6
    · exact hz.2.1 7
    · exact hz.2.1 8
    · exact hz.2.1 9
    · exact pair.1
    · exact pair.2
  refine ⟨hz.1, ?_, hz.2.2⟩
  intro e
  have idr : (fun k => (matchingRows p q π e k : ℝ)) =
      fun k => ∑ i, (c.recovery e i : ℝ) * (withPair (matchingRows p q σ) c.f c.g i k : ℝ) := by
    funext k
    exact_mod_cast recover e k
  exact rowspace_zero_certificate (fun i => (c.recovery e i : ℝ))
    (fun i k => (withPair (matchingRows p q σ) c.f c.g i k : ℝ)) z _ idr hk

theorem table_maximality_from_fibers {I : Type*} (p q : ℕ)
    (π : Fin 10 ≃ Fin 10) (block : Fin 10 → I)
    (bound : ∀ a b, (∀ z, TableHolds p q π z →
      qEval (shortForm p false a) z = qEval (shortForm p false b) z) → block a = block b)
    (reverse : ∀ g : ∀ i, {a // block a = i} ≃ {a // block a = i},
      ∀ z, TableHolds p q (π.trans (assembleFibers block g)) z → TableHolds p q π z) :
    ∀ σ : Fin 10 ≃ Fin 10,
      (∀ z, TableHolds p q π z → TableHolds p q σ z) →
      ∀ z, TableHolds p q σ z → TableHolds p q π z := by
  simp only [table_matching_locus_iff] at bound reverse ⊢
  exact maximality_from_fibers (TableChamber p q)
    (fun e z => qEval (shortForm p false e) z)
    (fun e z => qEval (shortForm q true e) z) π block bound reverse

#print axioms compact_reverse_sound
#print axioms table_maximality_from_fibers
end DifferenceTableResearch
