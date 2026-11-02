import Blueprint.A.AreaCalculus
import Mathlib.Data.Finset.Range

namespace Blueprint.Published
noncomputable section
open Companion ASector
open scoped BigOperators

def commutator (a b : FreeGroup Nat) : FreeGroup Nat := a*b*a⁻¹*b⁻¹

def houghtonS : FreeGroup Nat := commutator (FreeGroup.of 1) (FreeGroup.of 2)

/-- The four relators of P_H, paper equation (6.1). -/
def houghtonRelator (i : Fin 4) : FreeGroup Nat :=
  let p := FreeGroup.of 1
  let q := FreeGroup.of 2
  let s := houghtonS
  match i.val with
  | 0 => s^2
  | 1 => (s*p*s*p⁻¹)^3
  | 2 => commutator s (p^2*s*(p^2)⁻¹)
  | _ => p*s*p⁻¹*q*s⁻¹*q⁻¹

/-- Johnson's presentation P_J, Appendix A, with alpha numbered 3. -/
def johnsonRelator (i : Fin 5) : FreeGroup Nat :=
  let p := FreeGroup.of 1
  let q := FreeGroup.of 2
  let a := FreeGroup.of 3
  match i.val with
  | 0 => a^2
  | 1 => (a*p*a*p⁻¹)^3
  | 2 => commutator a (p^2*a*(p^2)⁻¹)
  | 3 => commutator p q*a⁻¹
  | _ => p*a*p⁻¹*q*a⁻¹*q⁻¹

def pointHom : FreeGroup Nat →* Equiv.Perm Concrete.Point := FreeGroup.lift fun j =>
  if j=1 then Concrete.pPoint else if j=2 then Concrete.qPoint else 1

def johnsonPointHom : FreeGroup Nat →* Equiv.Perm Concrete.Point := FreeGroup.lift fun j =>
  if j=1 then Concrete.pPoint else if j=2 then Concrete.qPoint
  else if j=3 then pointHom houghtonS else 1

def houghtonFiniteRelator (i : Fin 4) : FreeGroup (Fin 2) :=
  FreeGroup.map (fun j => (⟨(j-1)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)) (houghtonRelator i)

def johnsonFiniteRelator (i : Fin 5) : FreeGroup (Fin 3) :=
  FreeGroup.map (fun j => (⟨(j-1)%3,Nat.mod_lt _ (by decide)⟩ : Fin 3)) (johnsonRelator i)

def houghtonFiniteHom : FreeGroup (Fin 2) →* Equiv.Perm Concrete.Point :=
  pointHom.comp (FreeGroup.map (fun j => j.val+1))

def johnsonFiniteHom : FreeGroup (Fin 3) →* Equiv.Perm Concrete.Point :=
  johnsonPointHom.comp (FreeGroup.map (fun j => j.val+1))

def Fills {α : Type} {r : Nat} (R : Fin r → FreeGroup α) (H : FreeGroup α →* Equiv.Perm Concrete.Point)
    (n C : Nat) : Prop :=
  ∀ w : List (α × Bool), w.length≤n → H (FreeGroup.mk w)=1 →
    FiniteArea.Area R (FreeGroup.mk w) C

/-- The least uniform area bound; the finite-presentation assertion in
Corollary A.5 ensures that the fallback is never used for the cited inputs. -/
def dehn {α : Type} {r : Nat} (R : Fin r → FreeGroup α) (H : FreeGroup α →* Equiv.Perm Concrete.Point)
    (n : Nat) : Nat := by
  classical
  exact if h : ∃ C, Fills R H n C then Nat.find h else 0

def dehnH (n : Nat) : Nat := dehn houghtonFiniteRelator houghtonFiniteHom n
def dehnJ (n : Nat) : Nat := dehn johnsonFiniteRelator johnsonFiniteHom n

/-- Named literature input: Mghirbi--Douglas, released v1.0.0,
Corollary A.5 (cor:dehn-qp), including finiteness of both Dehn functions.
No term of this proposition is supplied by this module. -/
def HoughtonDehnCorollary : Prop := ∀ n : Nat, 1≤n →
  (∃ C, Fills houghtonFiniteRelator houghtonFiniteHom n C) ∧
  (∃ C, Fills johnsonFiniteRelator johnsonFiniteHom n C) ∧
  dehnH n≤dehnJ n ∧ (dehnJ n:ℝ)≤(2:ℝ)^((log2 n+6)^2)

/-- The certificate RP from paper Definition 7.1, as group relators. -/
def pauliCertificate : List (FreeGroup Nat) :=
  let p := FreeGroup.of 1
  let q := FreeGroup.of 2
  let t := FreeGroup.of 3
  let d := FreeGroup.of 4
  let x := FreeGroup.of 5
  let z := FreeGroup.of 6
  let s := houghtonS
  let B := p*s*p⁻¹
  let t2 := p*t*p⁻¹
  let t3 := p^2*t*(p^2)⁻¹
  [houghtonRelator 0,houghtonRelator 1,houghtonRelator 2,houghtonRelator 3,
   t^2,commutator t (s*p),commutator t (s*q),
   commutator d (B*s*p),commutator d (B*s*q),commutator t t2,
   d*t*d⁻¹*(t*t2)⁻¹,commutator d t2,commutator d t3,
   commutator p x,commutator p z,commutator q x,commutator q z,
   commutator d x,commutator d z,x^2,z^2,(x*z)^4,
   commutator x (t*x*t⁻¹),commutator x (t*z*t⁻¹),
   commutator z (t*x*t⁻¹),commutator z (t*z*t⁻¹),commutator (x*z*x*z) t]

def pauliRelator (i : Fin 27) : FreeGroup Nat := pauliCertificate[i.val]'(by have := i.isLt; simpa [pauliCertificate] using this)

end
end Blueprint.Published

#print axioms Blueprint.Published.commutator
#print axioms Blueprint.Published.houghtonS
#print axioms Blueprint.Published.houghtonRelator
#print axioms Blueprint.Published.johnsonRelator
#print axioms Blueprint.Published.pointHom
#print axioms Blueprint.Published.johnsonPointHom
#print axioms Blueprint.Published.houghtonFiniteRelator
#print axioms Blueprint.Published.johnsonFiniteRelator
#print axioms Blueprint.Published.houghtonFiniteHom
#print axioms Blueprint.Published.johnsonFiniteHom
#print axioms Blueprint.Published.Fills
#print axioms Blueprint.Published.dehn
#print axioms Blueprint.Published.dehnH
#print axioms Blueprint.Published.dehnJ
#print axioms Blueprint.Published.HoughtonDehnCorollary
#print axioms Blueprint.Published.pauliCertificate
#print axioms Blueprint.Published.pauliRelator
