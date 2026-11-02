import Blueprint.A.SpatialFiniteStrategy
import Blueprint.A.SpatialNaimarkProjective
import Blueprint.A.SpatialCoarseScore

namespace Blueprint.SpatialProof
noncomputable section
open Companion Companion.Analytic Published
open scoped BigOperators TensorProduct

theorem povm_to_finite_solution (hlit : TensorPerfectFinite) (g : LCS)
    (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (psi : SpatialTensor E F)
    (A : Fin g.system.equations.length → (Fin g.system.n → Bool) → E →L[ℂ] E)
    (B : Fin g.system.n → Bool → F →L[ℂ] F)
    (hpsi : ‖psi‖=1) (hv : validSpatial g A B) (hw : spatialWin g psi A B=1) :
    FiniteOperatorSolution g := by
  classical
  let I := Fin g.system.n → Bool
  let J : E →L[ℂ] NaimarkSpace I E := naimarkInclusion
  let K : F →L[ℂ] NaimarkSpace Bool F := naimarkInclusion
  let phi := (TensorProduct.mapL J K).completion psi
  let PA : (i : Fin g.system.equations.length) → PaperAnswer g i →
      NaimarkSpace I E →L[ℂ] NaimarkSpace I E :=
    fun i => coarseEffect (correctedRecord g i) (naimarkEffect (A i))
  let PB : Fin g.system.n → Bool → NaimarkSpace Bool F →L[ℂ] NaimarkSpace Bool F :=
    fun j => naimarkEffect (B j)
  have hAc (i : Fin g.system.equations.length) : ∑ a, A i a=1 := hv.2.1 i
  have hBc (j : Fin g.system.n) : ∑ b, B j b=1 := by
    simpa only [Fintype.sum_bool,add_comm,ContinuousLinearMap.one_def] using hv.2.2.2.2 j
  have hnorm : ‖phi‖=1 := by
    rw [tensor_lift_norm J K (naimarkInclusion_gram (I:=I) (E:=E))
      (naimarkInclusion_gram (I:=Bool) (E:=F)),hpsi]
  have hPA : ∀ i, PVM (PA i) := by
    intro i
    exact coarse_pvm (correctedRecord g i) (naimarkEffect (A i))
      (naimark_pvm (A i) (hv.1 i) (hAc i))
  have hPB : ∀ j, PVM (PB j) := fun j => naimark_pvm (B j) (hv.2.2.2.1 j) (hBc j)
  have hcompress (i : Fin g.system.equations.length) (a : PaperAnswer g i)
      (j : Fin g.system.n) (b : Bool) :
      expect phi (PA i a) (PB j b)=
        expect psi (coarseEffect (correctedRecord g i) (A i) a) (B j b) := by
    have hca := coarse_compression (correctedRecord g i) (naimarkEffect (A i)) (A i) J
      (naimark_compression (A i) (hv.1 i)) a
    have hcb : K.adjoint ∘L PB j b ∘L K=B j b := naimark_compression (B j) (hv.2.2.2.1 j) b
    rw [tensor_compression J K (PA i a) (PB j b) psi,hca,hcb]
  have hpoint : ∀ (i : Fin g.system.equations.length) (j : Fin g.system.n),
      j.val∈(g.system.equations[i.val]).vars →
      ∑ a : PaperAnswer g i, expect phi (PA i a) (PB j (ReturnProof.rowRecord g i a.val j))=1 := by
    intro i j hj
    calc
      _=∑ a : PaperAnswer g i, expect psi
          (coarseEffect (correctedRecord g i) (A i) a) (B j (ReturnProof.rowRecord g i a.val j)) :=
        Finset.sum_congr rfl (fun a ha => hcompress i a j _)
      _=∑ a : I, expect psi (A i a) (B j (ReturnProof.rowRecord g i (correctedRecord g i a).val j)) :=
        expect_coarse_sum psi (correctedRecord g i) (A i)
          (fun a => B j (ReturnProof.rowRecord g i a.val j))
      _=∑ a : I, expect psi (A i a) (B j (a j)) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hvalid : validAnswer g i a
        · rw [correctedRecord_bit g i a hvalid j hj]
        · rw [hv.2.2.1 i a hvalid,expect_zero_left,expect_zero_left]
      _=1 := (perfect_iff_pointwise g psi A B hpsi hv).mp hw i j hj
  exact hlit g (NaimarkSpace I E) (NaimarkSpace Bool F) phi PA PB hnorm hPA hPB hpoint

theorem spatial_exclusion_proof (hlit : TensorPerfectFinite) (g : LCS)
    (h : ∀ a b (s : Strategy g a b), win s≠1) : NoSpatialPerfect g := by
  intro E F _ _ _ _ _ _ psi A B hpsi hv hw
  have hs := povm_to_finite_solution hlit g E F psi A B hpsi hv hw
  obtain ⟨a,b,s,hs⟩ := finite_operator_strategy g hs
  exact h a b s hs

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.povm_to_finite_solution
#print axioms Blueprint.SpatialProof.spatial_exclusion_proof
