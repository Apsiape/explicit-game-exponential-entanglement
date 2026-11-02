import Blueprint.A.SpatialScore

namespace Blueprint.SpatialProof
noncomputable section
variable {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def embeddingSwap (J V : E →L[ℂ] K) : K →L[ℂ] K :=
  1-J ∘L J.adjoint-V ∘L V.adjoint+J ∘L V.adjoint+V ∘L J.adjoint

theorem four_comp {E₁ E₂ E₃ E₄ E₅ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
    [NormedAddCommGroup E₄] [NormedSpace ℂ E₄]
    [NormedAddCommGroup E₅] [NormedSpace ℂ E₅]
    (A : E₄ →L[ℂ] E₅) (B : E₃ →L[ℂ] E₄) (C : E₂ →L[ℂ] E₃) (D : E₁ →L[ℂ] E₂) :
    (A ∘L B) ∘L (C ∘L D)=(A ∘L (B ∘L C)) ∘L D := by
  ext x
  rfl

theorem embeddingSwap_adjoint (J V : E →L[ℂ] K) :
    (embeddingSwap J V).adjoint=embeddingSwap J V := by
  simp only [embeddingSwap,map_add,map_sub,
    ContinuousLinearMap.adjoint_one,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  abel

theorem embeddingSwap_square (J V : E →L[ℂ] K)
    (hJ : J.adjoint ∘L J=1) (hV : V.adjoint ∘L V=1)
    (hJV : J.adjoint ∘L V=0) (hVJ : V.adjoint ∘L J=0) :
    embeddingSwap J V*embeddingSwap J V=1 := by
  change (embeddingSwap J V) ∘L (embeddingSwap J V)=1
  simp only [embeddingSwap,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,
    four_comp,hJ,hV,hJV,hVJ,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  abel

theorem embeddingSwap_embedding (J V : E →L[ℂ] K)
    (hJ : J.adjoint ∘L J=1) (hVJ : V.adjoint ∘L J=0) :
    embeddingSwap J V ∘L J=V := by
  simp only [embeddingSwap,ContinuousLinearMap.add_comp,ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_assoc,hJ,hVJ,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,
    ContinuousLinearMap.id_comp,ContinuousLinearMap.comp_zero]
  abel

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.embeddingSwap
#print axioms Blueprint.SpatialProof.four_comp
#print axioms Blueprint.SpatialProof.embeddingSwap_adjoint
#print axioms Blueprint.SpatialProof.embeddingSwap_square
#print axioms Blueprint.SpatialProof.embeddingSwap_embedding
