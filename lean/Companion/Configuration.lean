import Companion.Kernel
import Mathlib.Data.Finset.Image
import Mathlib.Data.Bool.Basic
import Mathlib.GroupTheory.Perm.Basic
import Lean.Elab.Tactic.Omega

namespace Companion.Concrete

inductive Ray where
  | one | two | three
  deriving DecidableEq, BEq, Repr
abbrev Point := Ray × Nat
abbrev Config := Finset Point

def origin : Point := (.one,0)
def next : Point := (.one,1)

def pForward : Point → Point
  | (.one,h) => (.one,h+1)
  | (.two,0) => (.one,0)
  | (.two,h+1) => (.two,h)
  | (.three,h) => (.three,h)
def pBackward : Point → Point
  | (.one,0) => (.two,0)
  | (.one,h+1) => (.one,h)
  | (.two,h) => (.two,h+1)
  | (.three,h) => (.three,h)
def qForward : Point → Point
  | (.one,h) => (.one,h+1)
  | (.three,0) => (.one,0)
  | (.three,h+1) => (.three,h)
  | (.two,h) => (.two,h)
def qBackward : Point → Point
  | (.one,0) => (.three,0)
  | (.one,h+1) => (.one,h)
  | (.three,h) => (.three,h+1)
  | (.two,h) => (.two,h)
def swapPoint : Point → Point
  | (.one,h) => (.one,h)
  | (.two,h) => (.three,h)
  | (.three,h) => (.two,h)

def pPoint : Equiv.Perm Point where
  toFun := pForward
  invFun := pBackward
  left_inv := by rintro ⟨r,h⟩; cases r <;> cases h <;> rfl
  right_inv := by rintro ⟨r,h⟩; cases r <;> cases h <;> rfl
def qPoint : Equiv.Perm Point where
  toFun := qForward
  invFun := qBackward
  left_inv := by rintro ⟨r,h⟩; cases r <;> cases h <;> rfl
  right_inv := by rintro ⟨r,h⟩; cases r <;> cases h <;> rfl
def iPoint : Equiv.Perm Point where
  toFun := swapPoint
  invFun := swapPoint
  left_inv := by rintro ⟨r,h⟩; cases r <;> rfl
  right_inv := by rintro ⟨r,h⟩; cases r <;> rfl

def bit (v : Config) (y : Point) : Bool := decide (y ∈ v)
def flipConfig (y : Point) (v : Config) : Config :=
  if y ∈ v then v.erase y else insert y v

theorem flipConfig_involutive (y : Point) : Function.Involutive (flipConfig y) := by
  intro v
  apply Finset.ext
  intro z
  by_cases h : y ∈ v <;> by_cases he : z=y <;> simp [flipConfig,h,he]

theorem bit_flipConfig (p y : Point) (v : Config) :
    bit (flipConfig p v) y = (bit v y ^^ decide (y=p)) := by
  by_cases hp : p ∈ v <;> by_cases hy : y=p
  all_goals simp [bit,flipConfig,hp,hy]

def tConfig (y : Point) : Equiv.Perm Config :=
  ⟨flipConfig y,flipConfig y,flipConfig_involutive y,flipConfig_involutive y⟩

def dConfigFun (v : Config) : Config :=
  if origin ∈ v then flipConfig next v else v

theorem dConfigFun_involutive : Function.Involutive dConfigFun := by
  intro v
  have hn : origin ≠ next := by decide
  by_cases h : origin ∈ v
  · have he : origin ∈ flipConfig next v := by
      by_cases hh : next ∈ v <;> simp [flipConfig,hh,h,hn]
    simp only [dConfigFun,if_pos h,if_pos he]
    exact flipConfig_involutive next v
  · simp [dConfigFun,h]

def dConfig : Equiv.Perm Config :=
  ⟨dConfigFun,dConfigFun,dConfigFun_involutive,dConfigFun_involutive⟩

theorem bit_dConfig (v : Config) (y : Point) :
    bit (dConfig v) y = (bit v y ^^ (decide (y=next) && bit v origin)) := by
  change bit (dConfigFun v) y = _
  by_cases h : origin ∈ v
  · simpa [dConfigFun,h,bit] using bit_flipConfig next y v
  · simp [dConfigFun,h,bit]

theorem bit_mapConfig (e : Equiv.Perm Point) (v : Config) (y : Point) :
    bit (Equiv.finsetCongr e v) y = bit v (e.symm y) := by
  simp [bit,Finset.mem_map_equiv]

inductive HostLetter where
  | p | pinv | q | qinv | i | t | d
  deriving DecidableEq, Repr

def hostGenerator : HostLetter → Equiv.Perm Config
  | .p => Equiv.finsetCongr pPoint
  | .pinv => Equiv.finsetCongr pPoint.symm
  | .q => Equiv.finsetCongr qPoint
  | .qinv => Equiv.finsetCongr qPoint.symm
  | .i => Equiv.finsetCongr iPoint
  | .t => tConfig origin
  | .d => dConfig

def hostEval : List HostLetter → Equiv.Perm Config
  | [] => 1
  | a::w => hostGenerator a * hostEval w

/-- XOR sum over a finite list, with no quotient or untrusted normalization. -/
def parity {α : Type*} (f : α → Bool) : List α → Bool
  | [] => false
  | a::as => f a ^^ parity f as

def toggle {α : Type*} [DecidableEq α] (a : α) : List α → List α
  | [] => [a]
  | b::bs => if a=b then bs else b::toggle a bs

theorem parity_toggle {α : Type*} [DecidableEq α] (f : α → Bool) (a : α) (ls : List α) :
    parity f (toggle a ls) = (f a ^^ parity f ls) := by
  induction ls with
  | nil => simp [parity,toggle]
  | cons b bs ih =>
    by_cases h : a=b
    · subst b; simp [toggle,parity,Bool.xor_assoc]
    · simp only [toggle,if_neg h,parity,ih]
      cases f a <;> cases f b <;> cases parity f bs <;> rfl

def xorLists {α : Type*} [DecidableEq α] (a b : List α) : List α := a.foldr toggle b

theorem parity_xorLists {α : Type*} [DecidableEq α] (f : α → Bool) (a b : List α) :
    parity f (xorLists a b) = (parity f a ^^ parity f b) := by
  induction a with
  | nil => simp [xorLists,parity]
  | cons x xs ih =>
    change parity f (toggle x (xorLists xs b)) = _
    rw [parity_toggle,ih]
    simp only [parity,Bool.xor_assoc]

theorem parity_map {α β : Type*} (f : β → Bool) (g : α → β) (ls : List α) :
    parity f (ls.map g) = parity (f ∘ g) ls := by
  induction ls with
  | nil => rfl
  | cons a as ih => simp [parity,ih]

end Companion.Concrete
