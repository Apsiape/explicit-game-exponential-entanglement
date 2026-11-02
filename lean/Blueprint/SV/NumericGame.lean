import Blueprint.SV.EvenLift
import Blueprint.SV.NullAreas
import Blueprint.SV.GameRate
import Mathlib.Data.Fintype.Sort

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators

abbrev V := GeneralGadget.Variable balancedInput
abbrev E := GeneralGadget.EquationIndex balancedInput

def variableIndex : V ≃ Fin 406 := by
  letI : LE V := (GeneralGadget.variableOrder balancedInput).toLE
  letI : LT V := (GeneralGadget.variableOrder balancedInput).toLT
  letI : Preorder V := (GeneralGadget.variableOrder balancedInput).toPreorder
  letI : LinearOrder V := GeneralGadget.variableOrder balancedInput
  exact (monoEquivOfFin V balancedInput_sizes.1).symm.toEquiv

def equationIndex : E ≃ Fin 332 := Fintype.equivFinOfCardEq balancedInput_sizes.2

theorem variableIndex_increasing (a b : V)
    (h : @LT.lt V (GeneralGadget.variableOrder balancedInput).toLT a b) :
    (variableIndex a).val < (variableIndex b).val := by
  letI : LE V := (GeneralGadget.variableOrder balancedInput).toLE
  letI : LT V := (GeneralGadget.variableOrder balancedInput).toLT
  letI : Preorder V := (GeneralGadget.variableOrder balancedInput).toPreorder
  letI : LinearOrder V := GeneralGadget.variableOrder balancedInput
  exact (monoEquivOfFin V balancedInput_sizes.1).symm.strictMono h

def numericRow (i : Fin 332) : Companion.Equation :=
  let r := GeneralGadget.orderedEquation balancedInput (equationIndex.symm i)
  ⟨r.vars.map (fun a => (variableIndex a).val),r.rhs⟩

def numericSystem : Companion.Game := ⟨406,List.ofFn numericRow⟩

theorem typed_rows_nonempty (e : E) :
    (GeneralGadget.orderedEquation balancedInput e).vars≠[] := by
  have hpos : 0<(GeneralGadget.systemEquation balancedInput e).vars.length := by
    rcases e with e|⟨t,k⟩
    · rcases e with i|u|⟨a,b⟩|⟨t,b⟩
      · fin_cases i
        change 0<3
        omega
      · simp [GeneralGadget.systemEquation,GeneralGadget.niceEquation]
      · cases b <;> simp [GeneralGadget.systemEquation,GeneralGadget.niceEquation]
      · cases b <;> simp [GeneralGadget.systemEquation,GeneralGadget.niceEquation]
    · fin_cases k <;> simp [GeneralGadget.systemEquation]
  apply List.length_pos_iff.mp
  simpa only [GeneralGadget.orderedEquation,List.length_rotate] using hpos

theorem numeric_row_data (r : Companion.Equation) (hr : r∈numericSystem.equations) :
    r.vars≠[] ∧ r.vars.Nodup ∧ r.vars.Pairwise (· < ·) ∧
      (∀ j∈r.vars, j<numericSystem.n) ∧ r.vars.length≤3 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  let e := equationIndex.symm i
  have hinj : Function.Injective (fun a : V => (variableIndex a).val) := by
    intro a b hab
    exact variableIndex.injective (Fin.ext hab)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro hn
    change ((GeneralGadget.orderedEquation balancedInput e).vars.map
      (fun a => (variableIndex a).val))=[] at hn
    have hh := congrArg List.length hn
    rw [List.length_map,List.length_nil] at hh
    exact typed_rows_nonempty e (List.length_eq_zero_iff.mp hh)
  · exact (GeneralGadget.ordered_equation_nodup balancedInput e).map hinj
  · exact (GeneralGadget.ordered_equation_increasing balancedInput e).map
      (f:=fun a => (variableIndex a).val) (by intro a b hab; exact variableIndex_increasing a b hab)
  · intro j hj
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hj
    exact (variableIndex a).isLt
  · simpa only [numericRow,List.length_map] using GeneralGadget.ordered_equation_arity balancedInput e

theorem numeric_rows_exist : numericSystem.equations≠[] := by
  intro h
  have hh := congrArg List.length h
  change (List.ofFn numericRow).length=0 at hh
  rw [List.length_ofFn] at hh
  omega

theorem numeric_arity_attained : ∃ r∈numericSystem.equations, r.vars.length=3 := by
  let e : E := .inl (.inr (.inr (.inl (GeneralGadget.hT balancedInput,false))))
  let i := equationIndex e
  refine ⟨numericRow i,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
  simp [numericRow,i,e,GeneralGadget.orderedEquation,GeneralGadget.systemEquation,
    GeneralGadget.niceEquation]

def numericBase : LCS := MainProof.defaultLCS numericSystem
  (fun r hr => (numeric_row_data r hr).1)
  (fun r hr => (numeric_row_data r hr).2.1)
  (fun r hr => (numeric_row_data r hr).2.2.1)
  (fun r hr => (numeric_row_data r hr).2.2.2.1)
  numeric_rows_exist 3 (fun r hr => (numeric_row_data r hr).2.2.2.2)
  numeric_arity_attained

/-- The independent uniform equation/variable distribution of the SV game. -/
def numericGame : LCS := by
  refine { numericBase with
    pi := fun _ _ => 1/(332*406)
    pi_nonneg := by intros; norm_num
    pi_normalized := ?_
    piMin := 1/(332*406)
    piMin_pos := by norm_num
    piMin_lower := by intros; exact le_rfl
    piMin_attained := ?_ }
  · change (∑ i : Fin 332, ∑ j : Fin 406, (1/(332*406):ℝ))=1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  · let i : Fin numericSystem.equations.length := ⟨0,by
      change 0<(List.ofFn numericRow).length
      rw [List.length_ofFn]
      omega⟩
    have hr := List.getElem_mem i.isLt
    obtain ⟨j,hj⟩ := List.exists_mem_of_ne_nil _ ((numeric_row_data _ hr).1)
    exact ⟨i,⟨j,(numeric_row_data _ hr).2.2.2.1 j hj⟩,hj,rfl⟩

theorem numericGame_distribution (i : Fin numericGame.system.equations.length)
    (j : Fin numericGame.system.n) :
    numericGame.pi i j=1/((numericGame.system.equations.length:ℝ)*numericGame.system.n) := by
  change (1/(332*406):ℝ)=1/(((List.ofFn numericRow).length:ℝ)*406)
  simp only [List.length_ofFn]
  norm_num

end
end Blueprint.SV

#print axioms Blueprint.SV.V
#print axioms Blueprint.SV.E
#print axioms Blueprint.SV.variableIndex
#print axioms Blueprint.SV.equationIndex
#print axioms Blueprint.SV.variableIndex_increasing
#print axioms Blueprint.SV.numericRow
#print axioms Blueprint.SV.numericSystem
#print axioms Blueprint.SV.typed_rows_nonempty
#print axioms Blueprint.SV.numeric_row_data
#print axioms Blueprint.SV.numeric_rows_exist
#print axioms Blueprint.SV.numeric_arity_attained
#print axioms Blueprint.SV.numericBase
#print axioms Blueprint.SV.numericGame
#print axioms Blueprint.SV.numericGame_distribution
