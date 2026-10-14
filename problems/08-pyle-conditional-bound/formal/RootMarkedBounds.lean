import NodeJoin
import LocalQuotientLift

namespace Omnibus
namespace RootMarked

/-- A third-stack quality and a distinguished bass position in that stack. -/
structure HarmonicType where
  quality : Fin 11
  inversion : Fin 4
  deriving DecidableEq, BEq, Repr

deriving instance ReflBEq, LawfulBEq for HarmonicType

/-- Major, minor, diminished, augmented triads; then M7, 7, mM7, m7,
half-diminished, diminished seventh, augmented-major seventh. -/
def template (q : Fin 11) : List Nat :=
 match q.val with
 | 0 => [0,4,7]
 | 1 => [0,3,7]
 | 2 => [0,3,6]
 | 3 => [0,4,8]
 | 4 => [0,4,7,11]
 | 5 => [0,4,7,10]
 | 6 => [0,3,7,11]
 | 7 => [0,3,7,10]
 | 8 => [0,3,6,10]
 | 9 => [0,3,6,9]
 | _ => [0,4,8,11]

def relativeTemplate (h : HarmonicType) : List Nat :=
 (template h.quality).map fun n =>
   (n+12-(template h.quality)[h.inversion.val]!)%12

/-- Pitch-class set equality, preserving the distinguished root/inversion.
The stack itself supplies the root; no graph lookup defines this predicate. -/
def fits (q : Shape) (h : HarmonicType) : Bool :=
 h.inversion.val < (template h.quality).length &&
 [0,q.x,q.y,q.z].all (relativeTemplate h).contains &&
 (relativeTemplate h).all [0,q.x,q.y,q.z].contains

def allTypes : List HarmonicType :=
 (List.finRange 11).flatMap fun q => (List.finRange 4).map fun i => ⟨q,i⟩

def marks (q : Shape) : List HarmonicType := allTypes.filter (fits q)

/-- A root-marked harmonic reading of the actual ordered chord, modulo common
transposition and upper-voice order. Symmetric roots are not identified. -/
def Reads (c : Chord) (h : HarmonicType) : Prop := fits (sonority c) h = true

theorem allTypes_complete (h : HarmonicType) : h ∈ allTypes := by
 cases h
 simp [allTypes]

theorem marks_iff (q : Shape) (h : HarmonicType) :
 h ∈ marks q ↔ fits q h = true := by
 simp [marks, allTypes_complete]

def componentMarks (C : List Shape) : List HarmonicType :=
 (C.flatMap marks).eraseDups

/-- All finite checks are recomputed from Definitions 4–6. -/
def coreEntryCheck : Bool := checkedNodeList.all fun p =>
 (successors p).all fun q => (successors q).all fun r =>
 (successors r).all fun _ => core.contains q

theorem coreEntryChecked : coreEntryCheck = true := by decide

def componentCheck : Bool := coreSets.all fun C =>
 (componentMarks C).length ≤ 6 &&
 C.all (fun p => (successors p).all fun q => !core.contains q || C.contains q)

theorem componentsChecked : componentCheck = true := by decide

def separationCheck : Bool := core.all fun p =>
 (successors p).all fun q => (successors q).all fun r =>
 !core.contains q || !core.contains r ||
 (marks p).all (fun a => (marks q).all fun b => (marks r).all fun c =>
 a != b && a != c && b != c)

theorem separationChecked : separationCheck = true := by decide

theorem project {c d : Chord} (h : OmnibusStep c d) :
 sonority d ∈ successors (sonority c) :=
 (local_quotient_lift c h.1 (sonority d)).mpr ⟨d,h,rfl⟩

theorem entry_to_core {p q r s : Shape}
 (hp : p ∈ nodes) (hpq : q ∈ successors p)
 (hqr : r ∈ successors q) (hrs : s ∈ successors r) : q ∈ core := by
 have h := coreEntryChecked
 simp only [coreEntryCheck, List.all_eq_true, List.contains_iff] at h
 exact h p (nodes_exact ▸ hp) q hpq r hqr s hrs

theorem infinite_approachable_in_core (c : Nat → Chord)
 (hc : ∀ n, OmnibusStep (c n) (c (n+1)))
 (ha : ∃ p, OmnibusStep p (c 0)) : ∀ n, sonority (c n) ∈ core := by
 intro n
 cases n with
 | zero =>
   obtain ⟨p,hp⟩ := ha
   exact entry_to_core (chord_type_in_nodes p hp.1) (project hp)
     (project (hc 0)) (project (hc 1))
 | succ n =>
   exact entry_to_core (chord_type_in_nodes (c n) (hc n).1)
     (project (hc n)) (project (hc (n+1))) (project (hc (n+2)))

theorem component_data {C : List Shape} (hC : C ∈ coreSets) :
 (componentMarks C).length ≤ 6 ∧
 ∀ p ∈ C, ∀ q ∈ successors p, q ∈ core → q ∈ C := by
 have h := componentsChecked
 simp only [componentCheck, List.all_eq_true, Bool.and_eq_true,
   decide_eq_true_eq] at h
 obtain ⟨hlen,hclosed⟩ := h C hC
 refine ⟨hlen,?_⟩
 intro p hp q hq hcore
 have hg := hclosed p hp q hq
 have hb : core.contains q = true := List.contains_iff.mpr hcore
 simpa [hcore, List.contains_iff] using hg

theorem infinite_stays_in_component (c : Nat → Chord)
 (hc : ∀ n, OmnibusStep (c n) (c (n+1)))
 (ha : ∃ p, OmnibusStep p (c 0)) :
 ∃ C ∈ coreSets, ∀ n, sonority (c n) ∈ C := by
 have hcore := infinite_approachable_in_core c hc ha
 obtain ⟨C,hC,h0⟩ := List.mem_flatten.mp (hcore 0)
 refine ⟨C,hC,?_⟩
 intro n
 induction n with
 | zero => exact h0
 | succ n ih => exact (component_data hC).2 _ ih _ (project (hc n)) (hcore (n+1))

theorem separation {p q r : Shape} (hp : p ∈ core)
 (hpq : q ∈ successors p) (hq : q ∈ core)
 (hqr : r ∈ successors q) (hr : r ∈ core)
 {a b c : HarmonicType} (ha : a ∈ marks p) (hb : b ∈ marks q)
 (hc : c ∈ marks r) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
 have h := separationChecked
 simp only [separationCheck, List.all_eq_true] at h
 have hs := h p hp q hpq r hqr
 have hq' : core.contains q = true := List.contains_iff.mpr hq
 have hr' : core.contains r = true := List.contains_iff.mpr hr
 simp only [hq',hr',Bool.not_true,Bool.false_or,List.all_eq_true] at hs
 have hm := hs a ha b hb c hc
 simpa only [Bool.and_eq_true, bne_iff_ne, and_assoc] using hm

/-- Conditional 3–6 theorem for the complete range of root-marked sonorities.
The lower bound is witnessed already at indices 0,1,2. The upper bound covers
all indices, not just a finite prefix or the portion before a chosen extension. -/
theorem three_to_six (c : Nat → Chord) (h : Nat → HarmonicType)
 (hc : ∀ n, OmnibusStep (c n) (c (n+1)))
 (ha : ∃ p, OmnibusStep p (c 0))
 (hh : ∀ n, Reads (c n) (h n)) :
 (h 0 ≠ h 1 ∧ h 0 ≠ h 2 ∧ h 1 ≠ h 2) ∧
 ∃ L : List HarmonicType, L.length ≤ 6 ∧ ∀ n, h n ∈ L := by
 have hcore := infinite_approachable_in_core c hc ha
 have hm : ∀ n, h n ∈ marks (sonority (c n)) := fun n =>
   (marks_iff _ _).mpr (hh n)
 constructor
 · exact separation (hcore 0) (project (hc 0)) (hcore 1)
     (project (hc 1)) (hcore 2) (hm 0) (hm 1) (hm 2)
 · obtain ⟨C,hC,hpath⟩ := infinite_stays_in_component c hc ha
   refine ⟨componentMarks C,(component_data hC).1,?_⟩
   intro n
   apply List.mem_eraseDups.mpr
   exact List.mem_flatMap.mpr ⟨sonority (c n),hpath n,hm n⟩

#print axioms three_to_six
end RootMarked
end Omnibus
