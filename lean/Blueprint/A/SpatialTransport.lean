import Blueprint.A.SpatialScore

namespace Blueprint.SpatialProof
noncomputable section
open scoped TensorProduct
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
theorem completion_comp (A : F →L[ℂ] G) (B : E →L[ℂ] F) :
    (A ∘L B).completion=A.completion ∘L B.completion := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp

theorem tensor_transport (J : E →L[ℂ] G) (K : F →L[ℂ] H)
    (x : E ⊗[ℂ] F) (y : G ⊗[ℂ] H) :
    inner ℂ (TensorProduct.mapL J K x) y=
      inner ℂ x (TensorProduct.mapL J.adjoint K.adjoint y) := by
  induction x using TensorProduct.inductionOn with
  | tmul x₁ x₂ =>
    induction y using TensorProduct.inductionOn with
    | tmul y₁ y₂ =>
      simp only [TensorProduct.mapL_tmul,TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_right]
    | add y z hy hz => simp only [map_add,inner_add_right,hy,hz]
  | add x z hx hz => simp only [map_add,inner_add_left,hx,hz]

theorem completed_tensor_transport (J : E →L[ℂ] G) (K : F →L[ℂ] H)
    (x : SpatialTensor E F) (y : SpatialTensor G H) :
    inner ℂ ((TensorProduct.mapL J K).completion x) y=
      inner ℂ x ((TensorProduct.mapL J.adjoint K.adjoint).completion y) := by
  induction x,y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    simp only [ContinuousLinearMap.completion_apply_coe,UniformSpace.Completion.inner_coe]
    exact tensor_transport J K x y

theorem tensor_compression (J : E →L[ℂ] G) (K : F →L[ℂ] H)
    (P : G →L[ℂ] G) (Q : H →L[ℂ] H) (psi : SpatialTensor E F) :
    expect ((TensorProduct.mapL J K).completion psi) P Q=
      expect psi (J.adjoint ∘L P ∘L J) (K.adjoint ∘L Q ∘L K) := by
  unfold expect
  rw [completed_tensor_transport]
  have hh : (TensorProduct.mapL J.adjoint K.adjoint).completion ∘L
      (TensorProduct.mapL P Q).completion ∘L (TensorProduct.mapL J K).completion=
      (TensorProduct.mapL (J.adjoint ∘L P ∘L J) (K.adjoint ∘L Q ∘L K)).completion := by
    rw [←completion_comp,←completion_comp,←TensorProduct.mapL_comp,←TensorProduct.mapL_comp]
  change (inner ℂ psi (((TensorProduct.mapL J.adjoint K.adjoint).completion ∘L
      (TensorProduct.mapL P Q).completion ∘L (TensorProduct.mapL J K).completion) psi)).re=_
  rw [hh]

theorem tensor_lift_norm (J : E →L[ℂ] G) (K : F →L[ℂ] H)
    (hJ : J.adjoint ∘L J=1) (hK : K.adjoint ∘L K=1) (psi : SpatialTensor E F) :
    ‖(TensorProduct.mapL J K).completion psi‖=‖psi‖ := by
  have hh := completed_tensor_transport J K psi ((TensorProduct.mapL J K).completion psi)
  have hc : (TensorProduct.mapL J.adjoint K.adjoint).completion ∘L
      (TensorProduct.mapL J K).completion=ContinuousLinearMap.id ℂ _ := by
    rw [←completion_comp,←TensorProduct.mapL_comp,hJ,hK]
    simp only [ContinuousLinearMap.one_def,TensorProduct.mapL_id_id,completion_id]
  have he : inner ℂ ((TensorProduct.mapL J K).completion psi) ((TensorProduct.mapL J K).completion psi)=
      inner ℂ psi psi := by
    rw [hh]
    change inner ℂ psi (((TensorProduct.mapL J.adjoint K.adjoint).completion ∘L
      (TensorProduct.mapL J K).completion) psi)=_
    rw [hc,ContinuousLinearMap.id_apply]
  have hs := congrArg Complex.re he
  have h1 := inner_self_eq_norm_sq (𝕜:=ℂ) ((TensorProduct.mapL J K).completion psi)
  have h2 := inner_self_eq_norm_sq (𝕜:=ℂ) psi
  change (inner ℂ ((TensorProduct.mapL J K).completion psi) ((TensorProduct.mapL J K).completion psi)).re=
    (inner ℂ psi psi).re at hs
  have hsq := h1.symm.trans (hs.trans h2)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.completion_comp
#print axioms Blueprint.SpatialProof.tensor_transport
#print axioms Blueprint.SpatialProof.completed_tensor_transport
#print axioms Blueprint.SpatialProof.tensor_compression
#print axioms Blueprint.SpatialProof.tensor_lift_norm
