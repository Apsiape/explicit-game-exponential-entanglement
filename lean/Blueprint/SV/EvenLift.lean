import Blueprint.SV.BalancedInput
import Blueprint.W2.EvenRepresentation

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic Companion.DoubleMatrix

/-- The explicit even models, lifted through both removals and the solution-group
gadgets. All source and solution relators are the actual presentation relators. -/
theorem balanced_even_solution_lift (m : Nat) (hm : 0<m) :
    ∃ phi : FreeGroup (Option (GeneralGadget.Variable balancedInput)) →*
        U (Bool × (Bool × (Bool × Fin (2*m)))),
      (∀ i, defect (phi (GeneralGadget.solutionRelator balancedInput i)) ≤
        3*(Real.sqrt 2*Real.sin (Real.pi/(2*m)))) ∧
      phi (FreeGroup.of none)=ScalarPhase.minusOne _ ∧
      Fintype.card (Bool × (Bool × (Bool × Fin (2*m))))=16*m := by
  let U0 := W2.evenRepresentation m hm
  have hU0 : ∀ j, IsUnitary (U0 j) := W2.evenRepresentation_unitary m hm
  let H := assignmentHom U0 hU0
  let Q : Nat → U (Fin (2*m)) := fun j => H (FreeGroup.of j)
  have hexact (i : Fin 7) : H (FreeGroup.mk (kRelators.drop 1)[i])=1 := by
    apply Subtype.ext
    rw [assignmentHom_word]
    exact W2.evenRepresentation_exact m hm _ (List.getElem_mem i.isLt)
  have hA : Q 1*Q 1=1 := by
    simpa [H,Q,kRelators,assignmentHom,FreeGroup.lift_mk] using hexact 4
  have hB : Q 2*Q 2=1 := by
    simpa [H,Q,kRelators,assignmentHom,FreeGroup.lift_mk] using hexact 5
  have hC : Q 3=ScalarPhase.minusOne (Fin (2*m)) := by
    apply Subtype.ext
    simp [Q,H,assignmentHom,asUnitary,U0,W2.evenRepresentation,ScalarPhase.minusOne]
  have hYA : Q 5*Q 1*(Q 5)⁻¹=Q 2 := by
    apply eq_of_mul_inv_eq_one
    simpa [H,Q,kRelators,assignmentHom,FreeGroup.lift_mk,mul_assoc] using hexact 1
  have hYB : Q 5*Q 2*(Q 5)⁻¹=Q 1 := by
    apply eq_of_mul_inv_eq_one
    simpa [H,Q,kRelators,assignmentHom,FreeGroup.lift_mk,mul_assoc] using hexact 2
  have hlin : Q 1*Q 2*Q 3=1 := by
    have hab : (Q 3)⁻¹*(Q 1*Q 2)=1 := by
      simpa [H,Q,kRelators,assignmentHom,FreeGroup.lift_mk,mul_assoc] using hexact 3
    have hab' : Q 1*Q 2=Q 3 := by
      have hh := congrArg (fun z => Q 3*z) hab
      simpa [mul_assoc] using hh
    rw [hab',hC,ScalarPhase.square]
  have hAB : Commute (Q 1) (Q 2) := by
    have heq : Q 2=ScalarPhase.minusOne _ * Q 1 := by
      apply Subtype.ext
      simp [Q,H,assignmentHom,asUnitary,U0,W2.evenRepresentation,ScalarPhase.minusOne]
    rw [heq]
    exact (ScalarPhase.central (Q 1)).mul_right (Commute.refl _)
  have hX : Q 4=permutationUnitary (W2.shuffle m hm) := by
    apply Subtype.ext
    simp [Q,H,assignmentHom,asUnitary,U0,W2.evenRepresentation,permutationUnitary]
  obtain ⟨F,V,hF,hV,hFV⟩ := doubled_involutive_factorization (W2.shuffle m hm)
  rw [←hX] at hFV
  let e := Real.sqrt 2*Real.sin (Real.pi/(2*m))
  have hR : defect (powerResidual (Q 4) (Q 5))=e := by
    have hh := W2.evenRepresentation_first m hm
    have heq : H (FreeGroup.mk kRelators[0])=powerResidual (Q 4) (Q 5) := by
      simp [H,Q,kRelators,assignmentHom,FreeGroup.lift_mk,powerResidual,mul_assoc]
    have hword := assignmentHom_word U0 hU0 kRelators[0]
    change (H (FreeGroup.mk kRelators[0]):Mat (2*m))=wordEval U0 kRelators[0] at hword
    rw [heq] at hword
    simpa only [defect,sizeNorm,Fintype.card_fin,hword,normalizedHS,U0,e,
      div_eq_mul_inv,mul_comm] using hh
  have he : 0≤e := hR ▸ defect_nonneg (powerResidual (Q 4) (Q 5))
  obtain ⟨phi,hp,hJ,hcard⟩ := balanced_solution_lift (by simpa using (show 0<2*m by omega))
    (Q 1) (Q 2) (Q 3) (Q 4) (Q 5) F V hA hB hC hF hV hFV hAB hYA hYB hlin e he hR.le
  exact ⟨phi,hp,hJ,by simp; omega⟩

end
end Blueprint.SV

#print axioms Blueprint.SV.balanced_even_solution_lift
