import Blueprint.SV.AreaEncoding

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic

def numberedLetter : FinalAlphabet → FreeGroup Nat
  | none => FreeGroup.of 407
  | some a => FreeGroup.of ((variableIndex a).val+1)

def numberedHom : FreeGroup FinalAlphabet →* FreeGroup Nat := FreeGroup.lift numberedLetter

def rowIndex (e : E) : Fin numericSystem.equations.length :=
  ⟨(equationIndex e).val,by simpa only [numericSystem,List.length_ofFn] using (equationIndex e).isLt⟩

theorem typedEquation_rowIndex (e : E) : typedEquation (rowIndex e)=e := by
  change equationIndex.symm (equationIndex e)=e
  exact equationIndex.symm_apply_apply e

theorem mk_positive (vs : List Nat) :
    FreeGroup.mk (vs.map pos)=(vs.map (fun j => FreeGroup.of (j+1))).prod := by
  simpa [FreeGroup.lift_mk,List.map_map,Function.comp_def,pos] using
    (FreeGroup.lift_of_apply (FreeGroup.mk (vs.map pos))).symm

theorem numbered_row (e : E) :
    numberedHom (GeneralGadget.orderedRelator balancedInput (.inr (.inr (.inl e))))=
      FreeGroup.mk ((if numericSystem.equations[(rowIndex e).val].rhs then [pos 406] else [])++
        numericSystem.equations[(rowIndex e).val].vars.map pos) := by
  have hh := ordered_numeric_rows (rowIndex e)
  rw [typedEquation_rowIndex] at hh
  rw [←hh.1,←hh.2,←FreeGroup.mul_mk,mk_positive,List.map_map]
  cases he : (GeneralGadget.orderedEquation balancedInput e).rhs <;>
    simp [GeneralGadget.orderedRelator,numberedHom,numberedLetter,he,map_list_prod,
      List.map_map,Function.comp_def,pos,←FreeGroup.one_eq_mk,FreeGroup.of]

theorem numeric_J_square :
    let H := relationMap (relator numericSystem)
    H (FreeGroup.of 407)*H (FreeGroup.of 407)=1 := by
  have hh := relation_trivial (relator numericSystem) .centralSquare [pos 406,pos 406] rfl
  rw [group_word_eval] at hh
  simpa [pos] using hh

theorem numeric_ordered_trivial : ∀ i,
    relationMap (relator numericSystem) (numberedHom (GeneralGadget.orderedRelator balancedInput i))=1 := by
  let H := relationMap (relator numericSystem)
  intro i
  rcases i with a|a|e|⟨e,a,b⟩
  · cases a with
    | none => simpa [GeneralGadget.orderedRelator,numberedHom,numberedLetter] using numeric_J_square
    | some a =>
      let j := (variableIndex a).val
      have hh := relation_trivial (relator numericSystem) (.square j) [pos j,pos j]
        (by simp only [relator,show numericSystem.n=406 from rfl]; exact if_pos (variableIndex a).isLt)
      rw [group_word_eval] at hh
      simpa [GeneralGadget.orderedRelator,numberedHom,numberedLetter,j,pos] using hh
  · let j := (variableIndex a).val
    have hh := relation_trivial (relator numericSystem) (.central j)
      [pos j,pos 406,neg j,neg 406] (by
        simp only [relator,show numericSystem.n=406 from rfl]
        exact if_pos (variableIndex a).isLt)
    rw [group_word_eval] at hh
    simpa [GeneralGadget.orderedRelator,numberedHom,numberedLetter,j,pos,neg,mul_assoc] using hh
  · rw [numbered_row]
    apply relation_trivial _ (.equation (rowIndex e).val)
    have hb : numericSystem.equations[(rowIndex e).val].vars.all (· < 406)=true := by
      simp only [List.all_eq_true,decide_eq_true_eq]
      exact (numeric_row_data _ (List.getElem_mem (rowIndex e).isLt)).2.2.2.1
    simp only [relator,List.getElem?_eq_getElem (rowIndex e).isLt,Option.bind_some,
      show numericSystem.n=406 from rfl]
    change (if numericSystem.equations[(rowIndex e).val].vars.all (· < 406) then
      some ((if numericSystem.equations[(rowIndex e).val].rhs then [pos 406] else [])++
        numericSystem.equations[(rowIndex e).val].vars.map pos) else none)=_
    exact if_pos hb
  · classical
    by_cases hm : a∈(GeneralGadget.orderedEquation balancedInput e).vars ∧
        b∈(GeneralGadget.orderedEquation balancedInput e).vars
    · let j := (variableIndex a).val
      let k := (variableIndex b).val
      have hhrow := ordered_numeric_rows (rowIndex e)
      rw [typedEquation_rowIndex] at hhrow
      have ha : j∈numericSystem.equations[(rowIndex e).val].vars := by
        rw [←hhrow.1]
        exact List.mem_map.mpr ⟨a,hm.1,rfl⟩
      have hb : k∈numericSystem.equations[(rowIndex e).val].vars := by
        rw [←hhrow.1]
        exact List.mem_map.mpr ⟨b,hm.2,rfl⟩
      have hh := relation_trivial (relator numericSystem) (.commute (rowIndex e).val j k)
        [pos j,pos k,neg j,neg k] (by
          simp only [relator,List.getElem?_eq_getElem (rowIndex e).isLt,Option.bind_some]
          exact if_pos ⟨(variableIndex a).isLt,(variableIndex b).isLt,ha,hb⟩)
      rw [group_word_eval] at hh
      simpa [GeneralGadget.orderedRelator,hm,numberedHom,numberedLetter,j,k,pos,neg,mul_assoc] using hh
    · simp [GeneralGadget.orderedRelator,hm]

end
end Blueprint.SV

#print axioms Blueprint.SV.numberedLetter
#print axioms Blueprint.SV.numberedHom
#print axioms Blueprint.SV.rowIndex
#print axioms Blueprint.SV.typedEquation_rowIndex
#print axioms Blueprint.SV.mk_positive
#print axioms Blueprint.SV.numbered_row
#print axioms Blueprint.SV.numeric_J_square
#print axioms Blueprint.SV.numeric_ordered_trivial
