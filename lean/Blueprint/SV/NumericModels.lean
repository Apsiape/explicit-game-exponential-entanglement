import Blueprint.SV.NumericEncoding

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic Companion.DoubleMatrix

theorem solution_ordered_bound {α : Type} [Fintype α] [DecidableEq α]
    (phi : FreeGroup FinalAlphabet →* U α) (hJ : phi (FreeGroup.of none)=ScalarPhase.minusOne α)
    (e : ℝ) (hr : ∀ i, defect (phi (GeneralGadget.solutionRelator balancedInput i))≤e) :
    ∀ i, defect (phi (GeneralGadget.orderedRelator balancedInput i))≤e := by
  have hrow (q : E) :
      defect (phi (GeneralGadget.orderedRelator balancedInput (.inr (.inr (.inl q)))))=
        defect (phi (GeneralGadget.solutionRelator balancedInput (.inr (.inr (.inl q))))) := by
    let xs := (GeneralGadget.systemEquation balancedInput q).vars.map
      (fun a => phi (FreeGroup.of (some a)))
    let j := if (GeneralGadget.systemEquation balancedInput q).rhs then phi (FreeGroup.of none) else 1
    have hc : ∀ x∈xs, Commute j x := by
      intro x hx
      dsimp [j]
      split
      · rw [hJ]
        exact (ScalarPhase.central x).symm
      · exact Commute.one_left _
    have hh := phase_prod_rotate_length (DoubleMatrix.length (α:=α)) xs
      (GeneralGadget.rowRotation balancedInput q) j hc
    cases he : (GeneralGadget.systemEquation balancedInput q).rhs <;>
      simpa [GeneralGadget.orderedRelator,GeneralGadget.solutionRelator,GeneralGadget.orderedEquation,
        he,map_list_prod,List.map_map,Function.comp_def,List.map_rotate,xs,j,DoubleMatrix.length] using hh
  intro i
  rcases i with a|a|q|⟨q,a,b⟩
  · exact hr (.inl a)
  · exact hr (.inr (.inl a))
  · rw [hrow]
    exact hr (.inr (.inr (.inl q)))
  · have hi : GeneralGadget.orderedRelator balancedInput (.inr (.inr (.inr (q,a,b))))=
        GeneralGadget.solutionRelator balancedInput (.inr (.inr (.inr (q,a,b)))) := by
      dsimp only [GeneralGadget.orderedRelator,GeneralGadget.solutionRelator]
      rw [GeneralGadget.ordered_equation_mem,GeneralGadget.ordered_equation_mem]
    rw [hi]
    exact hr (.inr (.inr (.inr (q,a,b))))

theorem numeric_models (m : Nat) (hm : 0<m) :
    ∃ W : Nat → Mat (16*m), (∀ j, IsUnitary (W j)) ∧
      (∀ k r, relator numericGame.system k=some r →
        normalizedHS (wordEval W r-1)≤(3*Real.sqrt 2*Real.pi)/m) ∧
      W (numericGame.system.n+1)=-1 := by
  obtain ⟨phi,hrel,hJ,hcard⟩ := balanced_even_solution_lift m hm
  have hord := solution_ordered_bound phi hJ _ hrel
  let I : (Bool × (Bool × (Bool × Fin (2*m)))) ≃ Fin (16*m) := Fintype.equivFinOfCardEq hcard
  let H : FreeGroup Nat →* U (Fin (16*m)) := (AGadget.reindexUnitary I).comp (phi.comp typedLift)
  let W : Nat → Mat (16*m) := fun j => H (FreeGroup.of j)
  have hW : ∀ j, IsUnitary (W j) := fun j => (H (FreeGroup.of j)).property
  have hword (w : Word) : wordEval W w=(H (FreeGroup.mk w):Mat (16*m)) := by
    rw [←assignmentHom_word W hW]
    have hh : assignmentHom W hW=H := by
      apply FreeGroup.ext_hom
      intro j
      apply Subtype.ext
      simp only [assignmentHom,FreeGroup.lift_apply_of,asUnitary]
      rfl
    rw [hh]
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hsin : 3*(Real.sqrt 2*Real.sin (Real.pi/(2*m)))≤(3*Real.sqrt 2*Real.pi)/(m:ℝ) := by
    calc
      _ = (3*Real.sqrt 2)*Real.sin (Real.pi/(2*m)) := by ring
      _ ≤ (3*Real.sqrt 2)*(Real.pi/(2*m)) :=
        mul_le_mul_of_nonneg_left (Real.sin_le (by positivity)) (by positivity)
      _ ≤ (3*Real.sqrt 2)*(Real.pi/m) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_left Real.pi_pos.le hmR (by nlinarith)
      _ = _ := by ring
  refine ⟨W,hW,?_,?_⟩
  · intro key r hr
    change relator numericSystem key=some r at hr
    obtain ⟨i,hi⟩ := numeric_relator_typed key r hr
    rw [hword]
    have hn : normalizedHS ((H (FreeGroup.mk r):Mat (16*m))-1)=defect (H (FreeGroup.mk r)) := by
      simp only [normalizedHS,defect,sizeNorm,Fintype.card_fin,div_eq_mul_inv,mul_comm]
    rw [hn]
    change defect (AGadget.reindexUnitary I (phi (typedLift (FreeGroup.mk r))))≤_
    rw [AGadget.reindex_defect,hi]
    exact (hord i).trans hsin
  · change (AGadget.reindexUnitary I (phi (typedLift (FreeGroup.of 407))):Mat (16*m))=-1
    have ht : typedLift (FreeGroup.of 407)=FreeGroup.of none := by
      simp [typedLift,typed_letter_J]
    rw [ht,hJ]
    change Matrix.reindexAlgEquiv ℂ ℂ I (-1)=-1
    rw [map_neg,map_one]

theorem numeric_game_upper : quantumValueOne numericGame ∧
    ∃ C : ℝ, 0<C ∧ ∀ e, 0<e → e≤1 →
      gameDimensionProfile numericGame e≤ENNReal.ofReal (C/Real.sqrt e) := by
  exact game_rate_of_models numericGame (3*Real.sqrt 2*Real.pi) (by positivity) numeric_models

end
end Blueprint.SV

#print axioms Blueprint.SV.solution_ordered_bound
#print axioms Blueprint.SV.numeric_models
#print axioms Blueprint.SV.numeric_game_upper
