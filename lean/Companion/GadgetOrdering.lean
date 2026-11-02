import Companion.GeneralGadgetFormat
import Mathlib.Data.List.Rotate
import Mathlib.Order.Prod.Lex.Basic

namespace Companion.GeneralGadget
noncomputable section

def hostNumber (p : Input) : Host p → Nat
  | .inl a => a.val
  | .inr (.inl a) => p.n0+a.val
  | .inr (.inr (.inl a)) => p.n0+p.yCount+a.val
  | .inr (.inr (.inr (.inl a))) => p.n0+2*p.yCount+a.val
  | .inr (.inr (.inr (.inr false))) => p.n0+2*p.yCount+p.c1.length
  | .inr (.inr (.inr (.inr true))) => p.n0+2*p.yCount+p.c1.length+1
def tripleNumber (p : Input) : HostTriple p → Nat
  | .inl a => a.val
  | .inr (.inl (a,b)) => p.c0.length+2*a.val+b.toNat
  | .inr (.inr _) => p.c0.length+2*p.c1.length
def niceNumber (p : Input) : Nice p → Nat
  | .inl (k,a) => if k=0 then hostNumber p a else if k=1 then Fintype.card (Host p)+hostNumber p a else
    if k=2 then 2*Fintype.card (Host p)+hostNumber p a else 3*Fintype.card (Host p)+1+hostNumber p a
  | .inr (.inl _) => 3*Fintype.card (Host p)
  | .inr (.inr (t,b)) => 4*Fintype.card (Host p)+1+2*tripleNumber p t+b.toNat
def niceTripleNumber (p : Input) : NiceTriple p → Nat
  | .inl a => hostNumber p a
  | .inr (t,b) => Fintype.card (Host p)+2*tripleNumber p t+b.toNat
def variableNumber (p : Input) : Variable p → Nat
  | .inl a => niceNumber p a
  | .inr (t,k) => Fintype.card (Nice p)+7*niceTripleNumber p t+k.val

theorem host_positive (p : Input) : 0<Fintype.card (Host p) := by rw [host_card]; omega
theorem nice_card (p : Input) : Fintype.card (Nice p)=4*Fintype.card (Host p)+1+2*Fintype.card (HostTriple p) := by
  simp [Nice]; omega
theorem hostNumber_bound (p : Input) (a : Host p) : hostNumber p a<Fintype.card (Host p) := by
  rw [host_card]
  rcases a with a|a|a|a|b
  all_goals first
    | (have ha := a.isLt; simp only [hostNumber]; omega)
    | (cases b <;> simp only [hostNumber] <;> omega)
theorem tripleNumber_bound (p : Input) (a : HostTriple p) : tripleNumber p a<Fintype.card (HostTriple p) := by
  rw [hostTriple_card]
  rcases a with a|⟨a,b⟩|u
  · have ha := a.isLt; simp only [tripleNumber]; omega
  · have ha := a.isLt; cases b <;> simp [tripleNumber] <;> omega
  · simp [tripleNumber]
theorem niceNumber_bound (p : Input) (a : Nice p) : niceNumber p a<Fintype.card (Nice p) := by
  rw [nice_card]
  rcases a with ⟨k,a⟩|u|⟨t,b⟩
  · have ha := hostNumber_bound p a
    rw [host_card] at ha
    fin_cases k <;> simp [niceNumber] <;> omega
  · simp [niceNumber]; have hp := host_positive p; omega
  · have ht := tripleNumber_bound p t
    rw [hostTriple_card] at ht
    cases b <;> simp [niceNumber] <;> omega

/-- A numbering in the order used in Appendix B. Only strict inequalities
within a row matter; ties elsewhere may be broken by any finite enumeration. -/
theorem rows_cyclic_numbered (p : Input) (e : EquationIndex p) :
    ∃ k, ((systemEquation p e).vars.rotate k).Pairwise (fun a b => variableNumber p a<variableNumber p b) := by
  rcases e with e|⟨t,k⟩
  · rcases e with i|e
    · obtain ⟨k,hk⟩ := p.linear_order i
      refine ⟨k,?_⟩
      have hm : ((p.linear[i.val]).rotate k |>.map (fun a => old (nOld (hOld a)))).Pairwise
          (fun a b => variableNumber p a<variableNumber p b) := hk.map (f:=fun a => old (nOld (hOld a))) (by
        intro a b hab
        simpa [variableNumber,niceNumber,hostNumber,old,nOld,hOld] using hab)
      simpa [systemEquation,niceEquation,List.map_map,Function.comp_def,List.map_rotate] using hm
    · refine ⟨0,?_⟩
      rcases e with u|⟨a,k⟩|⟨t,k⟩
      · have hw := p.distinguished.isLt
        simp [systemEquation,niceEquation,old,nOld,hOld,hU,variableNumber,niceNumber,hostNumber]
        omega
      · have ha := hostNumber_bound p a
        have hp := host_positive p
        rw [host_card] at ha hp
        cases k <;> simp [systemEquation,niceEquation,old,nOld,nPrime,nDPrime,nBar,nG,variableNumber,niceNumber] <;> omega
      · rcases ht : hostTriple p t with ⟨a,b,c⟩
        have hb := hostNumber_bound p b
        have hc := hostNumber_bound p c
        rw [host_card] at hb hc
        cases k <;> simp [systemEquation,niceEquation,ht,old,nPrime,nDPrime,nK,variableNumber,niceNumber] <;> omega
  · refine ⟨0,?_⟩
    rcases ht : niceTriple p t with ⟨a,b,c⟩
    have ha := niceNumber_bound p a
    have hb := niceNumber_bound p b
    have hc := niceNumber_bound p c
    simp only [nice_card,host_card,hostTriple_card] at ha hb hc
    fin_cases k <;> simp [systemEquation,ht,old,lamp,variableNumber] <;> omega

def variableKey (p : Input) (a : Variable p) : Nat ×ₗ Fin (Fintype.card (Variable p)) :=
  toLex (variableNumber p a,Fintype.equivFin (Variable p) a)

def variableOrder (p : Input) : LinearOrder (Variable p) :=
  LinearOrder.lift' (variableKey p) (by
    intro a b h
    exact (Fintype.equivFin (Variable p)).injective (congrArg (fun x => (ofLex x).2) h))

def rowRotation (p : Input) (e : EquationIndex p) : Nat :=
  Classical.choose (rows_cyclic_numbered p e)

def orderedEquation (p : Input) (e : EquationIndex p) : Equation (Variable p) :=
  ⟨(systemEquation p e).vars.rotate (rowRotation p e),(systemEquation p e).rhs⟩

theorem ordered_equation_increasing (p : Input) (e : EquationIndex p) :
    (orderedEquation p e).vars.Pairwise (fun a b => @LT.lt _ (variableOrder p).toLT a b) := by
  have h := Classical.choose_spec (rows_cyclic_numbered p e)
  exact h.imp (by
    intro a b hab
    change variableKey p a < variableKey p b
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab))

theorem ordered_equation_arity (p : Input) (e : EquationIndex p) :
    (orderedEquation p e).vars.length≤3 := by
  simpa [orderedEquation] using equation_arity p e

theorem ordered_equation_nodup (p : Input) (e : EquationIndex p) :
    (orderedEquation p e).vars.Nodup := by
  simpa [orderedEquation] using equation_nodup p e

theorem ordered_equation_mem (p : Input) (e : EquationIndex p) (a : Variable p) :
    a ∈ (orderedEquation p e).vars ↔ a ∈ (systemEquation p e).vars := by
  simp [orderedEquation]

theorem ordered_equation_rhs (p : Input) (e : EquationIndex p) :
    (orderedEquation p e).rhs=true ↔ e=Sum.inl (Sum.inr (Sum.inl ())) :=
  equation_rhs p e

end
end Companion.GeneralGadget
