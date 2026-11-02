import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Companion

abbrev Word := List (Nat × Bool)

structure Equation where
  vars : List Nat
  rhs : Bool
  deriving DecidableEq, Repr

structure Game where
  n : Nat
  equations : List Equation
  deriving DecidableEq, Repr

structure Presentation where
  n0 : Nat
  c0 : List (Nat × Nat × Nat)
  c1 : List (Nat × Nat)
  linear : List (List Nat)
  distinguished : Nat
  deriving DecidableEq, Repr

inductive RelKey where
  | square (varIndex : Nat)
  | equation (row : Nat)
  | commute (row first second : Nat)
  | central (varIndex : Nat)
  | centralSquare
  | conjugacy (index : Nat)
  | pConjugacy (index : Nat)
  deriving DecidableEq, Repr

def pos (j : Nat) : Nat × Bool := (j + 1, true)
def neg (j : Nat) : Nat × Bool := (j + 1, false)

/-- Solution-group relators in the equation's recorded variable order.
`game_sorted` certifies that this is increasing for the supplied system. -/
def relator (g : Game) : RelKey → Option Word
  | .square j => if j < g.n then some [pos j, pos j] else none
  | .equation row => do
      let e ← g.equations[row]?
      if e.vars.all (· < g.n) then
        some ((if e.rhs then [pos g.n] else []) ++ e.vars.map pos)
      else none
  | .commute row j k => do
      let e ← g.equations[row]?
      if j < g.n ∧ k < g.n ∧ j ∈ e.vars ∧ k ∈ e.vars then
        some [pos j, pos k, neg j, neg k]
      else none
  | .central j => if j < g.n then some [pos j, pos g.n, neg j, neg g.n] else none
  | .centralSquare => some [pos g.n, pos g.n]
  | .conjugacy _ | .pConjugacy _ => none

def presentationRelator (p : Presentation) : RelKey → Option Word
  | .square j => if j < p.n0 then some [pos j, pos j] else none
  | .equation row => do
      let vs ← p.linear[row]?
      some (vs.map pos)
  | .conjugacy row => do
      let (a,b,c) ← p.c0[row]?
      some [pos a,pos b,pos a,neg c]
  | .pConjugacy row => do
      let (b,c) ← p.c1[row]?
      some [pos p.n0,pos b,neg p.n0,neg c]
  | _ => none

structure Factor where
  key : RelKey
  positive : Bool
  conjugator : Word
  deriving DecidableEq, Repr

def factorWordWith (rfn : RelKey → Option Word) (f : Factor) : Word :=
  let r := (rfn f.key).getD []
  f.conjugator ++ (if f.positive then r else FreeGroup.invRev r) ++
    FreeGroup.invRev f.conjugator

def expandWith (rfn : RelKey → Option Word) (fs : List Factor) : Word :=
  (fs.map (factorWordWith rfn)).flatten

/-- Explicit area witness: a product of at most `bound` conjugates of defining
relators or their inverses, equal to the target in the free group. No quotient
by the presentation is used to test the equality. -/
def HasAreaWith (rfn : RelKey → Option Word) (target : Word) (bound : Nat) : Prop :=
  ∃ fs : List Factor, fs.length ≤ bound ∧
    (∀ f ∈ fs, (rfn f.key).isSome = true) ∧
    FreeGroup.mk (expandWith rfn fs) = FreeGroup.mk target

def checkWith (rfn : RelKey → Option Word) (target : Word) (fs : List Factor) (bound : Nat) : Bool :=
  decide (fs.length ≤ bound) && fs.all (fun f => (rfn f.key).isSome) &&
    decide (FreeGroup.reduce (expandWith rfn fs) = FreeGroup.reduce target)

theorem checkWith_sound {rfn : RelKey → Option Word} {t : Word} {fs : List Factor} {b : Nat}
    (h : checkWith rfn t fs b = true) : HasAreaWith rfn t b := by
  simp only [checkWith, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨fs, h.1.1, List.all_eq_true.mp h.1.2, FreeGroup.reduce.exact h.2⟩

abbrev HasArea (g : Game) := HasAreaWith (relator g)
abbrev check (g : Game) := checkWith (relator g)
theorem check_sound {g : Game} {t : Word} {fs : List Factor} {b : Nat}
    (h : check g t fs b = true) : HasArea g t b := checkWith_sound h

end Companion
