import Companion.LocalGadgetScope
set_option maxHeartbeats 1000000

namespace Companion.GeneralGadget
noncomputable section
open DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

@[simp] theorem final_generator (p : Input) (gamma : Nice p → U α) (a : Variable p) :
    finalStageHom p gamma (FreeGroup.of (some a))=fourthStage p gamma a := by
  simp [finalStageHom,Option.elim_some]
@[simp] theorem fourth_old (p : Input) (gamma : Nice p → U α) (a : Nice p) :
    fourthStage p gamma (old a)=DoubleMatrix.copy (gamma a) := rfl
@[simp] theorem final_phase (p : Input) (gamma : Nice p → U α) :
    finalStageHom p gamma (FreeGroup.of none)=ScalarPhase.minusOne (Bool × α) := by
  simp [finalStageHom,Option.elim_none]

theorem local_bounds (p : Input) (gamma : Nice p → U α) (hc : 0<Fintype.card α)
    (eps : ℝ) (he : 0≤eps) (h : NiceApprox p gamma eps) (t : NiceTriple p) :
    ∀ r ∈ StageBlocks.stage4Relators,
      defect (finalStageHom p gamma (insertLocal p t (FreeGroup.mk r)))≤3*eps := by
  have hh : ∀ r ∈ StageBlocks.stage4Relators, defect (localPhi p gamma t (FreeGroup.mk r))≤3*eps := by
    rcases ht : niceTriple p t with ⟨a,b,c⟩
    simp only [localPhi,ht]
    apply StageValues.bounds4 hc _ _ _ eps he (h.square a) (h.square b) (h.square c)
    · simpa [ht] using h.conjugacy t
    · have hcomm : Commute (gamma b) (gamma c) := by simpa [ht] using h.nice_commutation t
      have heq : gamma b*gamma c*(gamma b)⁻¹*(gamma c)⁻¹=1 := by rw [hcomm.eq]; simp [mul_assoc]
      simpa [heq,defect_one] using he
  intro r hr
  have hb := hh r hr
  rw [← final_local,MonoidHom.comp_apply] at hb
  exact hb

theorem copied_product (p : Input) (gamma : Nice p → U α) (e : BaseEquation p) :
    finalStageHom p gamma (solutionRelator p (.inr (.inr (.inl (.inl e)))))=
      DoubleMatrix.copy ((if (niceEquation p e).rhs then ScalarPhase.minusOne α else 1)*
        ((niceEquation p e).vars.map gamma).prod) := by
  cases he : (niceEquation p e).rhs <;>
    simp [solutionRelator,systemEquation,he,final_phase,final_generator,fourth_old,
      map_list_prod,List.map_map,Function.comp_def,ScalarPhase.copy]

theorem local_commutation_bound (p : Input) (gamma : Nice p → U α) (hc : 0<Fintype.card α)
    (eps : ℝ) (he : 0≤eps) (h : NiceApprox p gamma eps) (t : NiceTriple p)
    (k : Fin 6) (i j : Fin 3) :
    defect (commWord (fourthStage p gamma (localVariable p t (localAt k i)))
      (fourthStage p gamma (localVariable p t (localAt k j))))≤3*eps := by
  have hb := local_bounds p gamma hc eps he h t _ (local_scope.2.2 k i j)
  rw [mk_commutator] at hb
  simp only [commWord,map_mul,map_inv] at hb
  rw [insertLocal_row p t k _ (localAt_mem k i),insertLocal_row p t k _ (localAt_mem k j)] at hb
  simpa only [final_generator,commWord] using hb

/-- Every final solution-group relator has defect at most 3 eps, including
both orientations of all row commutators and the central J relations. -/
theorem fourthStage_approx (p : Input) (gamma : Nice p → U α) (hc : 0<Fintype.card α)
    (eps : ℝ) (he : 0≤eps) (h : NiceApprox p gamma eps) :
    ∀ i, defect (finalStageHom p gamma (solutionRelator p i))≤3*eps := by
  intro i
  rcases i with a|i
  · cases a with
    | none => simpa [solutionRelator,finalStageHom,Option.elim_none,ScalarPhase.square,defect_one] using
        (mul_nonneg (by norm_num : (0:ℝ)≤3) he)
    | some a =>
      rcases a with a|⟨t,k⟩
      · have hb := copy_bound hc _ eps he (h.square a)
        rw [map_mul] at hb
        have hb' := hb.trans (show eps≤3*eps by linarith)
        simp only [solutionRelator,map_mul,final_generator]
        change defect (DoubleMatrix.copy (gamma a)*DoubleMatrix.copy (gamma a))≤3*eps
        exact hb'
      · have hmem : [(k.val+4,true),(k.val+4,true)] ∈ StageBlocks.stage4Relators := by
          simpa [Nat.add_assoc] using local_scope.1 (⟨k.val+3,by omega⟩:Fin 10)
        have hb := local_bounds p gamma hc eps he h t _ hmem
        rw [local_square_map] at hb
        simpa [solutionRelator,lamp] using hb
  · rcases i with a|i
    · have hcomm := ScalarPhase.central (fourthStage p gamma a)
      have heq : commWord (fourthStage p gamma a) (ScalarPhase.minusOne (Bool × α))=1 := by
        unfold commWord
        rw [hcomm.eq]
        simp [mul_assoc]
      have hn : defect (commWord (fourthStage p gamma a) (ScalarPhase.minusOne (Bool × α)))≤3*eps := by
        rw [heq,defect_one]
        positivity
      simpa only [solutionRelator,map_mul,map_inv,final_generator,final_phase,commWord] using hn
    · rcases i with e|⟨e,a,b⟩
      · rcases e with e|⟨t,k⟩
        · rw [copied_product]
          exact (copy_bound hc _ eps he (h.product e)).trans (by linarith)
        · have hb := local_bounds p gamma hc eps he h t _ (local_scope.2.1 k)
          rw [local_product_map] at hb
          exact hb
      · classical
        by_cases hm : a ∈ (systemEquation p e).vars ∧ b ∈ (systemEquation p e).vars
        · simp only [solutionRelator,if_pos hm,map_mul,map_inv,final_generator]
          change defect (commWord (fourthStage p gamma a) (fourthStage p gamma b))≤3*eps
          rcases e with e|⟨t,k⟩
          · have ha' : a ∈ (niceEquation p e).vars.map old := by simpa [systemEquation] using hm.1
            have hb' : b ∈ (niceEquation p e).vars.map old := by simpa [systemEquation] using hm.2
            obtain ⟨aa,haa,rfl⟩ := List.mem_map.mp ha'
            obtain ⟨bb,hbb,rfl⟩ := List.mem_map.mp hb'
            have hb := copy_bound hc _ (2*eps) (by positivity) (h.commutation e aa bb haa hbb)
            have heq : DoubleMatrix.copy (commWord (gamma aa) (gamma bb))=
                commWord (DoubleMatrix.copy (gamma aa)) (DoubleMatrix.copy (gamma bb)) := by
              simp only [commWord,map_mul,map_inv]
            rw [heq] at hb
            exact hb.trans (by linarith)
          · obtain ⟨ia,hia⟩ := local_row_position p t k a hm.1
            obtain ⟨ib,hib⟩ := local_row_position p t k b hm.2
            rw [← hia,← hib]
            exact local_commutation_bound p gamma hc eps he h t k ia ib
        · simpa [solutionRelator,hm,defect_one] using (mul_nonneg (by norm_num : (0:ℝ)≤3) he)

/-- The three-stage global matrix assignment, with its full final defect
bound. Its basis has cardinality 8d and J is exactly negative identity. -/
theorem G3 (p : Input) (d : Nat) (hd : 0<d)
    (phi : FreeGroup (Source p) →* U (Fin d)) (eps : ℝ) (he : 0≤eps)
    (hr : ∀ i, defect (phi (sourceRelator p i))≤eps)
    (hw : phi (srcOld p.distinguished)=ScalarPhase.minusOne (Fin d)) :
    (∀ i, defect (globalHom p phi (solutionRelator p i))≤3*eps) ∧
    (globalHom p phi (FreeGroup.of none):Matrix (Amplified (Fin d)) (Amplified (Fin d)) ℂ)=-1 ∧
    Fintype.card (Amplified (Fin d))=8*d := by
  have h1 := firstStage_approx p phi (by simpa using hd) eps he hr hw
  have h3 := thirdStage_approx p (firstStage p phi) (by simpa using hd) eps he h1
  have h4 := fourthStage_approx p (thirdStage p (firstStage p phi)) (by simpa using hd) eps he h3
  refine ⟨?_,global_J p phi,by simpa using (amplified_card (α:=Fin d))⟩
  exact h4

end
end Companion.GeneralGadget
