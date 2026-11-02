import Companion.GadgetOrdering
import Companion.FinalGadgetBounds
import Companion.CyclicProducts

namespace Companion.GeneralGadget
noncomputable section
set_option maxHeartbeats 500000

def orderedRelator (p : Input) : RelationIndex p → FreeGroup (Option (Variable p)) := by
  classical
  exact fun
  | .inl a => FreeGroup.of a*FreeGroup.of a
  | .inr (.inl a) => FreeGroup.of (some a)*FreeGroup.of none*(FreeGroup.of (some a))⁻¹*(FreeGroup.of none)⁻¹
  | .inr (.inr (.inl e)) =>
    (if (orderedEquation p e).rhs then FreeGroup.of none else 1)*
      ((orderedEquation p e).vars.map (fun a => FreeGroup.of (some a))).prod
  | .inr (.inr (.inr (e,a,b))) =>
    if a ∈ (orderedEquation p e).vars ∧ b ∈ (orderedEquation p e).vars then
      FreeGroup.of (some a)*FreeGroup.of (some b)*(FreeGroup.of (some a))⁻¹*(FreeGroup.of (some b))⁻¹
    else 1

abbrev OrderedSolutionGroup (p : Input) := PresentedGroup (Set.range (orderedRelator p))
def orderedX (p : Input) (a : Variable p) : OrderedSolutionGroup p := PresentedGroup.of (some a)
def orderedJ (p : Input) : OrderedSolutionGroup p := PresentedGroup.of none

private theorem commute_of_word {G : Type} [Group G] (a b : G) (h : a*b*a⁻¹*b⁻¹=1) : Commute a b := by
  change a*b=b*a
  have he : a*b*a⁻¹=b := eq_of_mul_inv_eq_one h
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun v => v*a) he

theorem ordered_central (p : Input) (a : Variable p) : Commute (orderedX p a) (orderedJ p) := by
  apply commute_of_word
  have h := PresentedGroup.one_of_mem (rels:=Set.range (orderedRelator p)) ⟨Sum.inr (Sum.inl a),rfl⟩
  simpa [orderedRelator,orderedX,orderedJ,PresentedGroup.of] using h

/-- Canonical generators of the ordered solution group satisfy every recorded
row as well. This is the exact presentation transport used for G1 and G2. -/
theorem ordered_canonical_solution (p : Input) : Solution (orderedX p) (orderedJ p) where
  square a := by
    have h := PresentedGroup.one_of_mem (rels:=Set.range (orderedRelator p)) ⟨Sum.inl (some a),rfl⟩
    simpa [orderedRelator,orderedX,PresentedGroup.of] using h
  j_square := by
    have h := PresentedGroup.one_of_mem (rels:=Set.range (orderedRelator p)) ⟨Sum.inl none,rfl⟩
    simpa [orderedRelator,orderedJ,PresentedGroup.of] using h
  central := ordered_central p
  product e := by
    have h := PresentedGroup.one_of_mem (rels:=Set.range (orderedRelator p))
      ⟨Sum.inr (Sum.inr (Sum.inl e)),rfl⟩
    let xs := (systemEquation p e).vars.map (orderedX p)
    let j : OrderedSolutionGroup p := if (systemEquation p e).rhs then orderedJ p else 1
    have hx : orderedX p=(fun a => PresentedGroup.mk (Set.range (orderedRelator p)) (FreeGroup.of (some a))) := rfl
    have hr : j*(xs.rotate (rowRotation p e)).prod=1 := by
      cases he : (systemEquation p e).rhs <;>
        simpa [orderedRelator,orderedEquation,he,orderedX,orderedJ,PresentedGroup.of,
          map_list_prod,List.map_map,Function.comp_def,List.map_rotate,xs,j,hx] using h
    have hc : ∀ x ∈ xs, Commute j x := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      dsimp [j]
      split
      · exact (ordered_central p a).symm
      · exact Commute.one_left _
    have ht := phase_prod_rotate_conjugate xs (rowRotation p e) j hc
    rw [hr] at ht
    let q := (xs.take (rowRotation p e%xs.length)).prod
    change j*xs.prod=1
    calc
      j*xs.prod=q*(q⁻¹*(j*xs.prod)*q)*q⁻¹ := by group
      _=1 := by rw [← ht]; group
  commutation e a b ha hb := by
    apply commute_of_word
    have h := PresentedGroup.one_of_mem (rels:=Set.range (orderedRelator p))
      ⟨Sum.inr (Sum.inr (Sum.inr (e,a,b))),rfl⟩
    have ha' := (ordered_equation_mem p e a).mpr ha
    have hb' := (ordered_equation_mem p e b).mpr hb
    simpa [orderedRelator,ha',hb',orderedX,PresentedGroup.of] using h

theorem ordered_evaluation (p : Input) :
    evaluateFinal (orderedX p) (orderedJ p)=PresentedGroup.mk (Set.range (orderedRelator p)) := by
  apply FreeGroup.ext_hom
  intro a
  cases a <;> simp [evaluateFinal,orderedX,orderedJ,PresentedGroup.of,Option.elim_none,Option.elim_some]

theorem ordered_G1_identity (p : Input) (i : SourceRel p) :
    PresentedGroup.mk (Set.range (orderedRelator p)) (substitution p (sourceRelator p i))=1 := by
  have h := (ordered_canonical_solution p).source_relators i
  simpa only [evaluateSource,MonoidHom.comp_apply,ordered_evaluation] using h

theorem ordered_G2_identity (p : Input) :
    PresentedGroup.mk (Set.range (orderedRelator p)) (distinguishedWord p)=1 := by
  have h := (ordered_canonical_solution p).distinguished_relation
  simpa only [ordered_evaluation] using h

theorem ordered_G1_G2 (p : Input) : ∃ A0 : Nat, 1≤A0 ∧
    (∀ i : SourceRel p, FiniteArea.Area (orderedRelator p) (substitution p (sourceRelator p i)) A0) ∧
    FiniteArea.Area (orderedRelator p) (distinguishedWord p) A0 := by
  let W : Option (SourceRel p) → FreeGroup (Option (Variable p)) :=
    fun i => i.elim (distinguishedWord p) (fun j => substitution p (sourceRelator p j))
  have hw : ∀ i, PresentedGroup.mk (Set.range (orderedRelator p)) (W i)=1 := by
    intro i
    cases i with
    | none => exact ordered_G2_identity p
    | some i => exact ordered_G1_identity p i
  obtain ⟨A,hA,hbound⟩ := FiniteArea.uniform_bound (orderedRelator p) W hw
  exact ⟨A,hA,fun i => hbound (some i),hbound none⟩

open DoubleMatrix

/-- Cyclically ordering a row preserves its defect exactly, because the
chosen J is central. No row commutation estimate is spent in this step. -/
theorem ordered_defect (p : Input) (d : Nat)
    (phi : FreeGroup (Source p) →* U (Fin d)) (e : EquationIndex p) :
    defect (globalHom p phi (orderedRelator p (.inr (.inr (.inl e)))))=
      defect (globalHom p phi (solutionRelator p (.inr (.inr (.inl e))))) := by
  let xs := (systemEquation p e).vars.map (fun a => globalHom p phi (FreeGroup.of (some a)))
  let j := if (systemEquation p e).rhs then globalHom p phi (FreeGroup.of none) else 1
  have hc : ∀ x ∈ xs, Commute j x := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    dsimp [j]
    split
    · exact (global_J_central p phi _).symm
    · exact Commute.one_left _
  have h := phase_prod_rotate_length (DoubleMatrix.length (α:=Amplified (Fin d))) xs (rowRotation p e) j hc
  cases he : (systemEquation p e).rhs <;>
    simpa [orderedRelator,solutionRelator,orderedEquation,he,map_list_prod,List.map_map,
      Function.comp_def,List.map_rotate,xs,j,DoubleMatrix.length] using h

theorem ordered_G3 (p : Input) (d : Nat) (hd : 0<d)
    (phi : FreeGroup (Source p) →* U (Fin d)) (eps : ℝ) (he : 0≤eps)
    (hr : ∀ i, defect (phi (sourceRelator p i))≤eps)
    (hw : phi (srcOld p.distinguished)=ScalarPhase.minusOne (Fin d)) :
    (∀ i, defect (globalHom p phi (orderedRelator p i))≤3*eps) ∧
    (globalHom p phi (FreeGroup.of none):Matrix (Amplified (Fin d)) (Amplified (Fin d)) ℂ)=-1 ∧
    Fintype.card (Amplified (Fin d))=8*d := by
  obtain ⟨h,hJ,hcard⟩ := G3 p d hd phi eps he hr hw
  refine ⟨?_,hJ,hcard⟩
  intro i
  rcases i with a|i
  · exact h (.inl a)
  · rcases i with a|i
    · exact h (.inr (.inl a))
    · rcases i with e|⟨e,a,b⟩
      · rw [ordered_defect]
        exact h (.inr (.inr (.inl e)))
      · have hh : orderedRelator p (.inr (.inr (.inr (e,a,b))))=
            solutionRelator p (.inr (.inr (.inr (e,a,b)))) := by
          dsimp only [orderedRelator,solutionRelator]
          rw [ordered_equation_mem,ordered_equation_mem]
        rw [hh]
        exact h (.inr (.inr (.inr (e,a,b))))

end
end Companion.GeneralGadget
