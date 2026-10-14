import Std

/-!
Kernel-checked finite certificates; see the verification receipts.
This file models Pyle's literal chord and move definitions, then states the
explicit bass-relative S3 quotient results. It does not formalize his undefined
word "extension" and does not claim to settle Conjecture 1.
No `sorry`, `axiom`, or `native_decide` is used. Compilation is pending.
-/
namespace Omnibus

structure Chord where
  bass : Nat
  tenor : Nat
  alto : Nat
  soprano : Nat
  deriving DecidableEq, BEq, Repr

structure Shape where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, BEq, Repr

-- The four coordinates of a chord must be representatives in Z/12Z.
def bounded (c : Chord) : Bool :=
  c.bass < 12 && c.tenor < 12 && c.alto < 12 && c.soprano < 12

def allDistinct (c : Chord) : Bool :=
  c.bass != c.tenor && c.bass != c.alto && c.bass != c.soprano &&
  c.tenor != c.alto && c.tenor != c.soprano && c.alto != c.soprano

def interval (a b : Nat) : Nat := (b + 12 - a) % 12

def third (n : Nat) : Bool := n == 3 || n == 4

-- This predicate is applied to a proposed stacking order, not a voicing.
def stacking (c : Chord) : Bool := Id.run do
  let d := interval c.bass c.tenor
  let e := interval c.tenor c.alto
  let f := interval c.alto c.soprano
  let triad := (d == 0 && third e && third f) ||
    (e == 0 && third d && third f) || (f == 0 && third d && third e)
  let seventh := allDistinct c && third d && third e && third f
  return triad || seventh

-- All 4! coordinate permutations, retaining duplicates for doubled pitches.
def reorderings (c : Chord) : List Chord :=
  let b := c.bass; let t := c.tenor; let a := c.alto; let s := c.soprano
  [⟨b,t,a,s⟩,⟨b,t,s,a⟩,⟨b,a,t,s⟩,⟨b,a,s,t⟩,⟨b,s,t,a⟩,⟨b,s,a,t⟩,
   ⟨t,b,a,s⟩,⟨t,b,s,a⟩,⟨t,a,b,s⟩,⟨t,a,s,b⟩,⟨t,s,b,a⟩,⟨t,s,a,b⟩,
   ⟨a,b,t,s⟩,⟨a,b,s,t⟩,⟨a,t,b,s⟩,⟨a,t,s,b⟩,⟨a,s,b,t⟩,⟨a,s,t,b⟩,
   ⟨s,b,t,a⟩,⟨s,b,a,t⟩,⟨s,t,b,a⟩,⟨s,t,a,b⟩,⟨s,a,b,t⟩,⟨s,a,t,b⟩]

-- Literal Definitions 4 and 5; no precomputed chord list occurs here.
def chord (c : Chord) : Bool := bounded c && (reorderings c).any stacking

-- v=0,1,2 means tenor, alto, soprano.
def step (v : Fin 3) (c : Chord) : Chord :=
  ⟨(c.bass + 11)%12,
   (c.tenor + if v.val == 0 then 1 else 0)%12,
   (c.alto + if v.val == 1 then 1 else 0)%12,
   (c.soprano + if v.val == 2 then 1 else 0)%12⟩

def back (v : Fin 3) (c : Chord) : Chord :=
  ⟨(c.bass + 1)%12,
   (c.tenor + if v.val == 0 then 11 else 0)%12,
   (c.alto + if v.val == 1 then 11 else 0)%12,
   (c.soprano + if v.val == 2 then 11 else 0)%12⟩

def OmnibusStep (c d : Chord) : Prop :=
  chord c = true ∧ chord d = true ∧ ∃ v : Fin 3, step v c = d

def voices : List (Fin 3) := [0,1,2]

def sort3 (x y z : Nat) : Shape :=
  let lo := min x (min y z)
  let hi := max x (max y z)
  ⟨lo,x+y+z-lo-hi,hi⟩

def sonority (c : Chord) : Shape :=
  sort3 ((c.tenor+12-c.bass)%12) ((c.alto+12-c.bass)%12)
    ((c.soprano+12-c.bass)%12)

def realize (q : Shape) : Chord := ⟨0,q.x,q.y,q.z⟩

def candidates : List Shape :=
  (List.range 12).flatMap fun x => (List.range 12).flatMap fun y =>
    ((List.range 12).filter fun z => x <= y && y <= z).map fun z => ⟨x,y,z⟩

def nodes : List Shape := candidates.filter (fun q => chord (realize q))

-- Recomputed from the literal chord predicate and actual ordered steps.
def successors (q : Shape) : List Shape :=
  ((voices.map fun v => step v (realize q)).filter chord).map sonority |>.eraseDups

-- The explicit distinction between a model definition and a graph certificate
-- matters: successors does not consult the graph table below.
def coreSets : List (List Shape) :=
 [[⟨0,4,7⟩,⟨1,5,9⟩,⟨2,5,8⟩,⟨3,6,10⟩,⟨3,7,9⟩,⟨4,8,11⟩],
  [⟨0,4,8⟩,⟨2,5,9⟩,⟨3,7,10⟩],
  [⟨0,5,8⟩,⟨1,4,8⟩,⟨2,6,9⟩,⟨3,5,9⟩,⟨3,7,11⟩,⟨4,7,10⟩],
  [⟨1,5,8⟩,⟨3,6,9⟩,⟨4,7,11⟩]]

def core : List Shape := coreSets.flatten

def entrances : List Shape := [⟨0,3,6⟩,⟨0,3,7⟩,⟨0,3,8⟩,⟨3,6,8⟩]
def exits : List Shape := [⟨0,4,9⟩,⟨0,5,9⟩,⟨0,6,9⟩,⟨4,6,9⟩]
def viable : List Shape := core ++ entrances

-- A complete bounded depth-first search, parameterized by allowed vertices.
-- Seen includes current. The number n counts further edges, not vertices.
def hasFreshWalk (allowed : List Shape) : Nat → List Shape → Shape → Bool
  | 0, _, _ => true
  | n+1, seen, current => (successors current).any fun next =>
      allowed.contains next && !(seen.contains next) &&
        hasFreshWalk allowed n (next::seen) next

def hasSimplePath (allowed : List Shape) (edges : Nat) : Bool :=
  allowed.any fun q => hasFreshWalk allowed edges [q] q

-- Finite certificates checked by kernel `decide`.



-- Finite counting representatives with fixed bass 0. Transposition acts freely
-- and supplies the factor 12 in the total counts. A universal equivariance
-- lemma and finite reordering completeness bridge still need to be supplied.
def zeroBassChords : List Chord :=
  (List.range 12).flatMap fun x => (List.range 12).flatMap fun y =>
    (List.range 12).map fun z => ⟨0,x,y,z⟩

def inImage (c : Chord) : Bool := voices.any fun v => chord (back v c)
def sourceRepresentatives : Nat := (zeroBassChords.filter chord).length
def imageRepresentatives : Nat := (zeroBassChords.filter inImage).length
def approachableRepresentatives : Nat :=
  (zeroBassChords.filter fun c => chord c && inImage c).length


theorem approachable_count_arithmetic : 12 * 186 = 2232 := by decide

def witness : List Chord :=
 [⟨0,0,3,6⟩,⟨11,0,3,7⟩,⟨10,1,3,7⟩,⟨9,1,4,7⟩,
  ⟨8,1,4,8⟩,⟨7,1,4,9⟩,⟨6,1,5,9⟩,⟨5,2,5,9⟩]

theorem witness_all_chords : witness.all chord = true := by decide
theorem witness_distinct_types : (witness.map sonority).eraseDups.length = 8 := by decide

-- Remaining semantic bridges are documented in FORMAL_STATUS.md.
theorem coordinate_permutations_complete :
    ∀ a b c d : Fin 4,
      allDistinct ⟨a.val,b.val,c.val,d.val⟩ = true ↔
      (reorderings ⟨0,1,2,3⟩).contains ⟨a.val,b.val,c.val,d.val⟩ = true := by decide

theorem modular_step_inverse : ∀ a : Fin 12,
    ((a.val+11)%12+1)%12 = a.val ∧
    ((a.val+1)%12+11)%12 = a.val := by decide

theorem witness_moves :
    step 2 ⟨0,0,3,6⟩ = ⟨11,0,3,7⟩ ∧
    step 0 ⟨11,0,3,7⟩ = ⟨10,1,3,7⟩ ∧
    step 1 ⟨10,1,3,7⟩ = ⟨9,1,4,7⟩ ∧
    step 2 ⟨9,1,4,7⟩ = ⟨8,1,4,8⟩ ∧
    step 2 ⟨8,1,4,8⟩ = ⟨7,1,4,9⟩ ∧
    step 1 ⟨7,1,4,9⟩ = ⟨6,1,5,9⟩ ∧
    step 0 ⟨6,1,5,9⟩ = ⟨5,2,5,9⟩ := by decide

#print axioms coordinate_permutations_complete
#print axioms modular_step_inverse
#print axioms witness_all_chords
#print axioms witness_distinct_types
#print axioms witness_moves
end Omnibus
