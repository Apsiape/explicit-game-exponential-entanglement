import Companion.GeneralGadgetForcing
import Companion.FiniteArea

namespace Companion.GeneralGadget
noncomputable section

abbrev RelationIndex (p : Input) := Option (Variable p) ⊕
  (Variable p ⊕ (EquationIndex p ⊕ (EquationIndex p × Variable p × Variable p)))

def solutionRelator (p : Input) : RelationIndex p → FreeGroup (Option (Variable p)) := by
  classical
  exact fun
  | .inl a => FreeGroup.of a*FreeGroup.of a
  | .inr (.inl a) => FreeGroup.of (some a)*FreeGroup.of none*(FreeGroup.of (some a))⁻¹*(FreeGroup.of none)⁻¹
  | .inr (.inr (.inl e)) =>
    (if (systemEquation p e).rhs then FreeGroup.of none else 1)*
      ((systemEquation p e).vars.map (fun a => FreeGroup.of (some a))).prod
  | .inr (.inr (.inr (e,a,b))) =>
    if a ∈ (systemEquation p e).vars ∧ b ∈ (systemEquation p e).vars then
      FreeGroup.of (some a)*FreeGroup.of (some b)*(FreeGroup.of (some a))⁻¹*(FreeGroup.of (some b))⁻¹
    else 1

abbrev SolutionGroup (p : Input) := PresentedGroup (Set.range (solutionRelator p))
def canonicalX (p : Input) (a : Variable p) : SolutionGroup p := PresentedGroup.of (some a)
def canonicalJ (p : Input) : SolutionGroup p := PresentedGroup.of none

private theorem commute_of_rel {G : Type} [Group G] (a b : G) (h : a*b*a⁻¹*b⁻¹=1) : Commute a b := by
  change a*b=b*a
  have he : a*b*a⁻¹=b := eq_of_mul_inv_eq_one h
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun v => v*a) he

theorem canonical_solution (p : Input) : Solution (canonicalX p) (canonicalJ p) where
  square a := by
    have h := PresentedGroup.one_of_mem (rels:=Set.range (solutionRelator p)) ⟨Sum.inl (some a),rfl⟩
    simpa [solutionRelator,canonicalX,PresentedGroup.of] using h
  j_square := by
    have h := PresentedGroup.one_of_mem (rels:=Set.range (solutionRelator p)) ⟨Sum.inl none,rfl⟩
    simpa [solutionRelator,canonicalJ,PresentedGroup.of] using h
  central a := by
    apply commute_of_rel
    have h := PresentedGroup.one_of_mem (rels:=Set.range (solutionRelator p)) ⟨Sum.inr (Sum.inl a),rfl⟩
    simpa [solutionRelator,canonicalX,canonicalJ,PresentedGroup.of] using h
  product e := by
    have h := PresentedGroup.one_of_mem (rels:=Set.range (solutionRelator p))
      ⟨Sum.inr (Sum.inr (Sum.inl e)),rfl⟩
    change (if (systemEquation p e).rhs then
      PresentedGroup.mk (Set.range (solutionRelator p)) (FreeGroup.of none) else 1)*
      ((systemEquation p e).vars.map (fun a =>
        PresentedGroup.mk (Set.range (solutionRelator p)) (FreeGroup.of (some a)))).prod=1
    cases he : (systemEquation p e).rhs <;>
      simpa [solutionRelator,he,canonicalX,canonicalJ,PresentedGroup.of,map_list_prod,
        List.map_map,Function.comp_def] using h
  commutation e a b ha hb := by
    apply commute_of_rel
    have h := PresentedGroup.one_of_mem (rels:=Set.range (solutionRelator p))
      ⟨Sum.inr (Sum.inr (Sum.inr (e,a,b))),rfl⟩
    simpa [solutionRelator,ha,hb,canonicalX,PresentedGroup.of] using h

theorem canonical_evaluation (p : Input) :
    evaluateFinal (canonicalX p) (canonicalJ p)=PresentedGroup.mk (Set.range (solutionRelator p)) := by
  apply FreeGroup.ext_hom
  intro a
  cases a <;> simp [evaluateFinal,canonicalX,canonicalJ,PresentedGroup.of,Option.elim_none,Option.elim_some]

theorem G1_identity (p : Input) (i : SourceRel p) :
    PresentedGroup.mk (Set.range (solutionRelator p)) (substitution p (sourceRelator p i))=1 := by
  have h := (canonical_solution p).source_relators i
  simpa only [evaluateSource,MonoidHom.comp_apply,canonical_evaluation] using h

theorem G2_identity (p : Input) :
    PresentedGroup.mk (Set.range (solutionRelator p)) (distinguishedWord p)=1 := by
  have h := (canonical_solution p).distinguished_relation
  simpa only [canonical_evaluation] using h

/-- Universal G1-G2, for every permitted source presentation. The bound is
the area of an actual finite product of conjugates in the final presentation. -/
theorem G1_G2 (p : Input) : ∃ A0 : Nat, 1≤A0 ∧
    (∀ i : SourceRel p, FiniteArea.Area (solutionRelator p) (substitution p (sourceRelator p i)) A0) ∧
    FiniteArea.Area (solutionRelator p) (distinguishedWord p) A0 := by
  let W : Option (SourceRel p) → FreeGroup (Option (Variable p)) :=
    fun i => i.elim (distinguishedWord p) (fun j => substitution p (sourceRelator p j))
  have hw : ∀ i, PresentedGroup.mk (Set.range (solutionRelator p)) (W i)=1 := by
    intro i
    cases i with
    | none => exact G2_identity p
    | some i => exact G1_identity p i
  obtain ⟨A,hA,hbound⟩ := FiniteArea.uniform_bound (solutionRelator p) W hw
  exact ⟨A,hA,fun i => hbound (some i),hbound none⟩

end
end Companion.GeneralGadget
