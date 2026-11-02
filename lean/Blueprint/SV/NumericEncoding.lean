import Blueprint.SV.NumericGame
import Blueprint.AGadget

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic

def decodeVariable (j : Nat) : V := variableIndex.symm (Fin.ofNat 406 j)

theorem decode_variable_index (a : V) : decodeVariable (variableIndex a).val=a := by
  have he : Fin.ofNat 406 (variableIndex a).val=variableIndex a :=
    Fin.ext (Nat.mod_eq_of_lt (variableIndex a).isLt)
  rw [decodeVariable,he,Equiv.symm_apply_apply]

def typedEquation (i : Fin numericSystem.equations.length) : E :=
  equationIndex.symm ⟨i.val,by simpa only [numericSystem,List.length_ofFn] using i.isLt⟩

theorem ordered_numeric_rows (i : Fin numericSystem.equations.length) :
    (GeneralGadget.orderedEquation balancedInput (typedEquation i)).vars.map
        (fun a => (variableIndex a).val)=numericSystem.equations[i.val].vars ∧
      (GeneralGadget.orderedEquation balancedInput (typedEquation i)).rhs=
        numericSystem.equations[i.val].rhs := by
  constructor <;> simp only [numericSystem,List.getElem_ofFn,numericRow,typedEquation]

theorem decode_numeric_row (i : Fin numericSystem.equations.length) :
    numericSystem.equations[i.val].vars.map decodeVariable=
      (GeneralGadget.orderedEquation balancedInput (typedEquation i)).vars := by
  rw [←(ordered_numeric_rows i).1,List.map_map]
  simp only [Function.comp_def,decode_variable_index]
  exact List.map_id _

def typedLetter (j : Nat) : FreeGroup FinalAlphabet :=
  if j=407 then FreeGroup.of none else
    if 1≤j ∧ j≤406 then FreeGroup.of (some (decodeVariable (j-1))) else 1

def typedLift : FreeGroup Nat →* FreeGroup FinalAlphabet := FreeGroup.lift typedLetter

theorem typed_letter_variable (j : Nat) (hj : j<406) :
    typedLetter (j+1)=FreeGroup.of (some (decodeVariable j)) := by
  unfold typedLetter
  rw [if_neg (by omega : j+1≠407),if_pos (by omega : 1≤j+1 ∧ j+1≤406)]
  simp only [Nat.add_sub_cancel]

theorem typed_letter_J : typedLetter 407=FreeGroup.of none := by simp [typedLetter]

theorem typed_lift_positive (vs : List Nat) (hb : ∀ j∈vs, j<406) :
    typedLift (FreeGroup.mk (vs.map pos))=
      (vs.map (fun j => FreeGroup.of (some (decodeVariable j)))).prod := by
  simp only [typedLift,FreeGroup.lift_mk,List.map_map,Function.comp_def,pos,↓reduceIte]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  exact typed_letter_variable j (hb j hj)

theorem typed_lift_row (i : Fin numericSystem.equations.length) :
    typedLift (FreeGroup.mk ((if numericSystem.equations[i.val].rhs then [pos 406] else [])++
      numericSystem.equations[i.val].vars.map pos))=
        GeneralGadget.orderedRelator balancedInput (.inr (.inr (.inl (typedEquation i)))) := by
  classical
  rw [←FreeGroup.mul_mk,map_mul,typed_lift_positive _ (by
    intro j hj
    exact (numeric_row_data _ (List.getElem_mem i.isLt)).2.2.2.1 j hj)]
  have hm : numericSystem.equations[i.val].vars.map
        (fun j => FreeGroup.of (some (decodeVariable j)))=
      (GeneralGadget.orderedEquation balancedInput (typedEquation i)).vars.map
        (fun a => FreeGroup.of (some a)) := by
    rw [←decode_numeric_row,List.map_map]
    rfl
  rw [hm]
  dsimp only [GeneralGadget.orderedRelator]
  rw [(ordered_numeric_rows i).2]
  cases hh : numericSystem.equations[i.val].rhs <;>
    simp [typedLift,FreeGroup.lift_mk,pos,typed_letter_J,←FreeGroup.one_eq_mk]

theorem numeric_relator_typed (key : RelKey) (r : Word) (hr : relator numericSystem key=some r) :
    ∃ i : GeneralGadget.RelationIndex balancedInput,
      typedLift (FreeGroup.mk r)=GeneralGadget.orderedRelator balancedInput i := by
  classical
  cases key with
  | square j =>
    simp only [relator] at hr
    split at hr
    next hj =>
      cases Option.some.inj hr
      refine ⟨.inl (some (decodeVariable j)),?_⟩
      simp [typedLift,FreeGroup.lift_mk,pos,typed_letter_variable j hj,GeneralGadget.orderedRelator]
    next => cases hr
  | centralSquare =>
    cases Option.some.inj hr
    refine ⟨.inl none,?_⟩
    simp [typedLift,FreeGroup.lift_mk,pos,typed_letter_J,GeneralGadget.orderedRelator,
      show numericSystem.n=406 from rfl]
  | central j =>
    simp only [relator] at hr
    split at hr
    next hj =>
      cases Option.some.inj hr
      refine ⟨.inr (.inl (decodeVariable j)),?_⟩
      simp [typedLift,FreeGroup.lift_mk,pos,neg,typed_letter_variable j hj,typed_letter_J,
        GeneralGadget.orderedRelator,mul_assoc,show numericSystem.n=406 from rfl]
    next => cases hr
  | equation row =>
    simp only [relator] at hr
    cases hg : numericSystem.equations[row]? with
    | none => simp [hg] at hr
    | some eqn =>
      simp only [hg,Option.bind_some] at hr
      change (if eqn.vars.all (· < 406) then
        some ((if eqn.rhs then [pos 406] else [])++eqn.vars.map pos) else none)=some r at hr
      split at hr
      next =>
        cases Option.some.inj hr
        obtain ⟨hidx,heq⟩ := List.getElem?_eq_some_iff.mp hg
        subst eqn
        exact ⟨.inr (.inr (.inl (typedEquation ⟨row,hidx⟩))),typed_lift_row ⟨row,hidx⟩⟩
      next => cases hr
  | commute row j k =>
    simp only [relator] at hr
    cases hg : numericSystem.equations[row]? with
    | none => simp [hg] at hr
    | some eqn =>
      simp only [hg,Option.bind_some] at hr
      change (if j<406 ∧ k<406 ∧ j∈eqn.vars ∧ k∈eqn.vars then
        some [pos j,pos k,neg j,neg k] else none)=some r at hr
      split at hr
      next hc =>
        cases Option.some.inj hr
        obtain ⟨hidx,heq⟩ := List.getElem?_eq_some_iff.mp hg
        subst eqn
        let q := typedEquation (⟨row,hidx⟩:Fin numericSystem.equations.length)
        have hm (j : Nat) (hj : j∈numericSystem.equations[row].vars) :
            decodeVariable j∈(GeneralGadget.orderedEquation balancedInput q).vars := by
          have hh : decodeVariable j∈numericSystem.equations[row].vars.map decodeVariable :=
            List.mem_map.mpr ⟨j,hj,rfl⟩
          rwa [decode_numeric_row ⟨row,hidx⟩] at hh
        refine ⟨.inr (.inr (.inr (q,decodeVariable j,decodeVariable k))),?_⟩
        simp [typedLift,FreeGroup.lift_mk,pos,neg,typed_letter_variable j hc.1,
          typed_letter_variable k hc.2.1,GeneralGadget.orderedRelator,
          hm j hc.2.2.1,hm k hc.2.2.2,mul_assoc]
      next => cases hr
  | conjugacy _ => cases hr
  | pConjugacy _ => cases hr

end
end Blueprint.SV

#print axioms Blueprint.SV.decodeVariable
#print axioms Blueprint.SV.decode_variable_index
#print axioms Blueprint.SV.typedEquation
#print axioms Blueprint.SV.ordered_numeric_rows
#print axioms Blueprint.SV.decode_numeric_row
#print axioms Blueprint.SV.typedLetter
#print axioms Blueprint.SV.typedLift
#print axioms Blueprint.SV.typed_letter_variable
#print axioms Blueprint.SV.typed_letter_J
#print axioms Blueprint.SV.typed_lift_positive
#print axioms Blueprint.SV.typed_lift_row
#print axioms Blueprint.SV.numeric_relator_typed
