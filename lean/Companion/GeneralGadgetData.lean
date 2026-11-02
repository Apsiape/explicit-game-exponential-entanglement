import Companion.Gadget
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Companion.GeneralGadget

/-- Precisely the finite EGamma0 data with at most one non-involutive letter.
The linear commutations are listed in C0, rather than added as assumptions
about a representation. Empty linear sets are allowed. -/
structure Input where
  n0 : Nat
  hasY : Bool
  distinguished : Fin n0
  c0 : List (Fin n0 × Fin n0 × Fin n0)
  c1 : List (Fin n0 × Fin n0)
  c1_absent : hasY=false → c1=[]
  linear : List (List (Fin n0))
  linear_nodup : ∀ i : Fin linear.length, (linear[i]).Nodup
  linear_small : ∀ i : Fin linear.length, (linear[i]).length≤3
  linear_order : ∀ i : Fin linear.length, ∃ k, ((linear[i]).rotate k).Pairwise (· < ·)
  linear_commutations : ∀ i : Fin linear.length, ∀ a ∈ linear[i], ∀ b ∈ linear[i], a≠b →
    (a,b,b) ∈ c0 ∨ (b,a,a) ∈ c0

def Input.yCount (p : Input) : Nat := if p.hasY then 1 else 0
abbrev Source (p : Input) := Fin p.n0 ⊕ Fin p.yCount
abbrev SourceRel (p : Input) := Fin p.n0 ⊕ (Fin p.linear.length ⊕ (Fin p.c0.length ⊕ Fin p.c1.length))

def Input.yIndex (p : Input) (i : Fin p.c1.length) : Fin p.yCount := ⟨0,by
  cases h : p.hasY
  · have hz := p.c1_absent h
    have hi := i.isLt
    simp [hz] at hi
  · simp [Input.yCount,h]⟩

def srcOld {p : Input} (a : Fin p.n0) : FreeGroup (Source p) := FreeGroup.of (.inl a)
def srcY {p : Input} (a : Fin p.yCount) : FreeGroup (Source p) := FreeGroup.of (.inr a)

def sourceRelator (p : Input) : SourceRel p → FreeGroup (Source p)
  | .inl a => srcOld a*srcOld a
  | .inr (.inl i) => ((p.linear[i]).map srcOld).prod
  | .inr (.inr (.inl i)) =>
    let (a,b,c) := p.c0[i]
    srcOld a*srcOld b*srcOld a*(srcOld c)⁻¹
  | .inr (.inr (.inr i)) =>
    let (b,c) := p.c1[i]
    srcY (p.yIndex i)*srcOld b*(srcY (p.yIndex i))⁻¹*(srcOld c)⁻¹

abbrev Host (p : Input) := Fin p.n0 ⊕ (Fin p.yCount ⊕ (Fin p.yCount ⊕ (Fin p.c1.length ⊕ Bool)))
def hOld {p : Input} (a : Fin p.n0) : Host p := .inl a
def hF {p : Input} (a : Fin p.yCount) : Host p := .inr (.inl a)
def hV {p : Input} (a : Fin p.yCount) : Host p := .inr (.inr (.inl a))
def hZ {p : Input} (a : Fin p.c1.length) : Host p := .inr (.inr (.inr (.inl a)))
def hT (p : Input) : Host p := .inr (.inr (.inr (.inr false)))
def hU (p : Input) : Host p := .inr (.inr (.inr (.inr true)))
abbrev HostTriple (p : Input) := Fin p.c0.length ⊕ ((Fin p.c1.length × Bool) ⊕ Unit)

def hostTriple (p : Input) : HostTriple p → Host p × Host p × Host p
  | .inl i => let (a,b,c) := p.c0[i]; (hOld a,hOld b,hOld c)
  | .inr (.inl (i,false)) => let (b,_) := p.c1[i]; (hV (p.yIndex i),hOld b,hZ i)
  | .inr (.inl (i,true)) => let (_,c) := p.c1[i]; (hF (p.yIndex i),hZ i,hOld c)
  | .inr (.inr _) => (hT p,hOld p.distinguished,hU p)

abbrev Nice (p : Input) := (Fin 4 × Host p) ⊕ (Unit ⊕ (HostTriple p × Bool))
def nOld {p : Input} (a : Host p) : Nice p := .inl (0,a)
def nPrime {p : Input} (a : Host p) : Nice p := .inl (1,a)
def nDPrime {p : Input} (a : Host p) : Nice p := .inl (2,a)
def nBar {p : Input} (a : Host p) : Nice p := .inl (3,a)
def nG (p : Input) : Nice p := .inr (.inl ())
def nK {p : Input} (a : HostTriple p) (b : Bool) : Nice p := .inr (.inr (a,b))
abbrev NiceTriple (p : Input) := Host p ⊕ (HostTriple p × Bool)

def niceTriple (p : Input) : NiceTriple p → Nice p × Nice p × Nice p
  | .inl a => (nG p,nPrime a,nDPrime a)
  | .inr (t,false) => let (a,b,c) := hostTriple p t; (nBar a,nPrime b,nDPrime c)
  | .inr (t,true) => let (a,b,c) := hostTriple p t; (nBar a,nDPrime b,nPrime c)

structure Equation (T : Type) where
  vars : List T
  rhs : Bool

abbrev BaseEquation (p : Input) := Fin p.linear.length ⊕ (Unit ⊕ ((Host p × Bool) ⊕ (HostTriple p × Bool)))

def niceEquation (p : Input) : BaseEquation p → Equation (Nice p)
  | .inl i => ⟨(p.linear[i]).map (fun a => nOld (hOld a)),false⟩
  | .inr (.inl _) => ⟨[nOld (hOld p.distinguished),nOld (hU p)],true⟩
  | .inr (.inr (.inl (a,false))) => ⟨[nOld a,nPrime a,nDPrime a],false⟩
  | .inr (.inr (.inl (a,true))) => ⟨[nOld a,nG p,nBar a],false⟩
  | .inr (.inr (.inr (t,false))) =>
    let (_,b,c) := hostTriple p t
    ⟨[nPrime b,nDPrime c,nK t false],false⟩
  | .inr (.inr (.inr (t,true))) =>
    let (_,b,c) := hostTriple p t
    ⟨[nPrime c,nDPrime b,nK t true],false⟩

abbrev Variable (p : Input) := Nice p ⊕ (NiceTriple p × Fin 7)
abbrev EquationIndex (p : Input) := BaseEquation p ⊕ (NiceTriple p × Fin 6)
def old {p : Input} (a : Nice p) : Variable p := .inl a
def lamp {p : Input} (t : NiceTriple p) (k : Fin 7) : Variable p := .inr (t,k)

def systemEquation (p : Input) : EquationIndex p → Equation (Variable p)
  | .inl e => ⟨(niceEquation p e).vars.map old,(niceEquation p e).rhs⟩
  | .inr (t,k) =>
    let (a,b,c) := niceTriple p t
    let y := lamp t
    ⟨if k=0 then [old a,y 0,y 1] else
      if k=1 then [old b,y 1,y 2] else
      if k=2 then [y 2,y 3,y 4] else
      if k=3 then [old a,y 4,y 5] else
      if k=4 then [old c,y 5,y 6] else [y 0,y 3,y 6],false⟩

def sourceImages (p : Input) : Source p → FreeGroup (Option (Variable p))
  | .inl a => FreeGroup.of (some (old (nOld (hOld a))))
  | .inr a => FreeGroup.of (some (old (nOld (hF a))))*FreeGroup.of (some (old (nOld (hV a))))
def substitution (p : Input) : FreeGroup (Source p) →* FreeGroup (Option (Variable p)) :=
  FreeGroup.lift (sourceImages p)

def distinguishedWord (p : Input) : FreeGroup (Option (Variable p)) :=
  let w := FreeGroup.of (some (old (nOld (hOld p.distinguished))))
  let t := FreeGroup.of (some (old (nOld (hT p))))
  w*t*w⁻¹*t⁻¹*FreeGroup.of none

theorem host_card (p : Input) : Fintype.card (Host p)=p.n0+2*p.yCount+p.c1.length+2 := by
  simp [Host]; omega
theorem hostTriple_card (p : Input) : Fintype.card (HostTriple p)=p.c0.length+2*p.c1.length+1 := by
  simp [HostTriple]; omega
theorem variable_card (p : Input) : Fintype.card (Variable p)=
    11*Fintype.card (Host p)+16*Fintype.card (HostTriple p)+1 := by
  simp [Variable,Nice,NiceTriple]
  ring
theorem equation_card (p : Input) : Fintype.card (EquationIndex p)=
    p.linear.length+1+8*Fintype.card (Host p)+14*Fintype.card (HostTriple p) := by
  simp [EquationIndex,BaseEquation,NiceTriple]
  ring

theorem equation_arity (p : Input) (e : EquationIndex p) : (systemEquation p e).vars.length≤3 := by
  rcases e with i|⟨t,k⟩
  · rcases i with i|i
    · simpa [systemEquation,niceEquation] using p.linear_small i
    · rcases i with u|i
      · simp [systemEquation,niceEquation]
      · rcases i with ⟨a,b⟩|⟨t,b⟩ <;> cases b <;> simp [systemEquation,niceEquation]
  · fin_cases k <;> simp [systemEquation]

theorem equation_rhs (p : Input) (e : EquationIndex p) :
    (systemEquation p e).rhs=true ↔ e=Sum.inl (Sum.inr (Sum.inl ())) := by
  rcases e with i|⟨t,k⟩
  · rcases i with i|i
    · simp [systemEquation,niceEquation]
    · rcases i with u|i
      · cases u; simp [systemEquation,niceEquation]
      · rcases i with ⟨a,b⟩|⟨t,b⟩ <;> cases b <;> simp [systemEquation,niceEquation]
  · simp [systemEquation]

end Companion.GeneralGadget
