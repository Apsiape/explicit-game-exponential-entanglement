import Companion.OrderedGadget

namespace Companion.GeneralGadget
noncomputable section

/-- The full general gadget statement. All output data (the binary matrix,
rows, substitution, special variable and matrix assignment) are the explicit
definitions above, rather than existentially supplied certificates. -/
def Lemma : Prop := ∀ p : Input,
  (∀ e, (orderedEquation p e).vars.Pairwise (fun a b => @LT.lt _ (variableOrder p).toLT a b)) ∧
  (∀ e, (orderedEquation p e).vars.Nodup ∧ (orderedEquation p e).vars.length≤3) ∧
  (∀ e a, coefficient p e a=true ↔ a ∈ (orderedEquation p e).vars) ∧
  (∀ e, (orderedEquation p e).rhs=true ↔ e=Sum.inl (Sum.inr (Sum.inl ()))) ∧
  Fintype.card (Variable p)=11*Fintype.card (Host p)+16*Fintype.card (HostTriple p)+1 ∧
  Fintype.card (EquationIndex p)=p.linear.length+1+8*Fintype.card (Host p)+14*Fintype.card (HostTriple p) ∧
  (∃ A0 : Nat, 1≤A0 ∧
    (∀ i, PresentedGroup.mk (Set.range (orderedRelator p)) (substitution p (sourceRelator p i))=1 ∧
      FiniteArea.Area (orderedRelator p) (substitution p (sourceRelator p i)) A0) ∧
    PresentedGroup.mk (Set.range (orderedRelator p)) (distinguishedWord p)=1 ∧
    FiniteArea.Area (orderedRelator p) (distinguishedWord p) A0) ∧
  (∀ (d : Nat), 0<d → ∀ (phi : FreeGroup (Source p) →* DoubleMatrix.U (Fin d)) (eps : ℝ),
    0≤eps → (∀ i, DoubleMatrix.defect (phi (sourceRelator p i))≤eps) →
    phi (srcOld p.distinguished)=ScalarPhase.minusOne (Fin d) →
    (∀ i, DoubleMatrix.defect (globalHom p phi (orderedRelator p i))≤3*eps) ∧
    (globalHom p phi (FreeGroup.of none):Matrix (Amplified (Fin d)) (Amplified (Fin d)) ℂ)=-1 ∧
    Fintype.card (Amplified (Fin d))=8*d)

theorem gadgetLemma : Lemma := by
  intro p
  refine ⟨ordered_equation_increasing p,fun e => ⟨ordered_equation_nodup p e,ordered_equation_arity p e⟩,
    ?_,ordered_equation_rhs p,variable_card p,equation_card p,?_,ordered_G3 p⟩
  · intro e a
    exact (coefficient_spec p e a).trans (ordered_equation_mem p e a).symm
  · obtain ⟨A,hA,h1,h2⟩ := ordered_G1_G2 p
    exact ⟨A,hA,fun i => ⟨ordered_G1_identity p i,h1 i⟩,ordered_G2_identity p,h2⟩

end
end Companion.GeneralGadget
