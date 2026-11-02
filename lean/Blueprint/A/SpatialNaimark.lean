import Blueprint.A.SpatialBlocks

namespace Blueprint.SpatialProof
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I]

abbrev NaimarkSpace (I E : Type*) := BlockSpace (Option I) E

def naimarkColumn (A : I → E →L[ℂ] E) : E →L[ℂ] NaimarkSpace I E :=
  blockStack (fun a : Option I => match a with
    | none => 0
    | some a => CFC.sqrt (A a))

def naimarkInclusion : E →L[ℂ] NaimarkSpace I E := blockInclude none

theorem naimarkInclusion_gram :
    (naimarkInclusion (I:=I) (E:=E)).adjoint ∘L naimarkInclusion=1 := by
  simp [naimarkInclusion,blockInclude_adjoint,block_project_include]

theorem naimarkColumn_gram (A : I → E →L[ℂ] E)
    (hA : ∀ a, positiveOperator (A a)) (hAc : ∑ a, A a=1) :
    (naimarkColumn A).adjoint ∘L naimarkColumn A=1 := by
  rw [naimarkColumn,blockStack_gram]
  have hs a : (CFC.sqrt (A a)).adjoint=CFC.sqrt (A a) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hsq a : CFC.sqrt (A a) ∘L CFC.sqrt (A a)=A a :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr ((positive_iff _).mp (hA a)))
  simpa [Fintype.sum_option,hs,hsq] using hAc

theorem naimarkInclusion_column (A : I → E →L[ℂ] E) :
    (naimarkInclusion (I:=I)).adjoint ∘L naimarkColumn A=0 := by
  rw [naimarkInclusion,blockInclude_adjoint,naimarkColumn,blockStack_component]

theorem naimarkColumn_inclusion (A : I → E →L[ℂ] E) :
    (naimarkColumn A).adjoint ∘L naimarkInclusion=0 := by
  have hh := congrArg ContinuousLinearMap.adjoint (naimarkInclusion_column A)
  simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,map_zero] using hh

def naimarkSwap (A : I → E →L[ℂ] E) : NaimarkSpace I E →L[ℂ] NaimarkSpace I E :=
  embeddingSwap naimarkInclusion (naimarkColumn A)

theorem naimarkSwap_adjoint (A : I → E →L[ℂ] E) :
    (naimarkSwap A).adjoint=naimarkSwap A := embeddingSwap_adjoint _ _

theorem naimarkSwap_square (A : I → E →L[ℂ] E)
    (hA : ∀ a, positiveOperator (A a)) (hAc : ∑ a, A a=1) :
    naimarkSwap A*naimarkSwap A=1 :=
  embeddingSwap_square _ _ naimarkInclusion_gram (naimarkColumn_gram A hA hAc)
    (naimarkInclusion_column A) (naimarkColumn_inclusion A)

theorem naimarkSwap_inclusion (A : I → E →L[ℂ] E) :
    naimarkSwap A ∘L naimarkInclusion=naimarkColumn A :=
  embeddingSwap_embedding _ _ naimarkInclusion_gram (naimarkColumn_inclusion A)

def naimarkOutcome (a : I) : NaimarkSpace I E →L[ℂ] NaimarkSpace I E :=
  blockProjection (some a)+if a=default then blockProjection none else 0

theorem naimarkOutcome_adjoint (a : I) :
    (naimarkOutcome (E:=E) a).adjoint=naimarkOutcome a := by
  by_cases h : a=default <;>
    simp [naimarkOutcome,h,map_add,blockProjection_adjoint]

theorem naimarkOutcome_square (a : I) :
    naimarkOutcome (E:=E) a*naimarkOutcome a=naimarkOutcome a := by
  by_cases h : a=default <;>
    simp [naimarkOutcome,h,add_mul,mul_add,blockProjection_mul]

theorem naimarkOutcome_sum : ∑ a : I, naimarkOutcome (E:=E) a=1 := by
  have hh := blockProjection_sum (E:=E) (I:=Option I)
  simp only [Fintype.sum_option] at hh
  simpa [naimarkOutcome,Finset.sum_add_distrib,add_comm] using hh

def naimarkEffect (A : I → E →L[ℂ] E) (a : I) :
    NaimarkSpace I E →L[ℂ] NaimarkSpace I E :=
  naimarkSwap A ∘L naimarkOutcome a ∘L naimarkSwap A

theorem naimarkEffect_adjoint (A : I → E →L[ℂ] E) (a : I) :
    (naimarkEffect A a).adjoint=naimarkEffect A a := by
  simp only [naimarkEffect,ContinuousLinearMap.adjoint_comp,naimarkSwap_adjoint,
    naimarkOutcome_adjoint,ContinuousLinearMap.comp_assoc]

theorem naimarkEffect_square (A : I → E →L[ℂ] E)
    (hA : ∀ a, positiveOperator (A a)) (hAc : ∑ a, A a=1) (a : I) :
    naimarkEffect A a*naimarkEffect A a=naimarkEffect A a := by
  let U := naimarkSwap A
  let Q := naimarkOutcome (E:=E) a
  have hU : U ∘L U=1 := naimarkSwap_square A hA hAc
  have hQ : Q ∘L Q=Q := naimarkOutcome_square a
  change ((U ∘L Q) ∘L U) ∘L ((U ∘L Q) ∘L U)=(U ∘L Q) ∘L U
  calc
    _=U ∘L Q ∘L (U ∘L U) ∘L Q ∘L U := by simp only [ContinuousLinearMap.comp_assoc]
    _=U ∘L (Q ∘L Q) ∘L U := by simp only [hU,ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp,ContinuousLinearMap.comp_assoc]
    _=_ := by rw [hQ]; simp only [ContinuousLinearMap.comp_assoc]

theorem naimarkEffect_sum (A : I → E →L[ℂ] E)
    (hA : ∀ a, positiveOperator (A a)) (hAc : ∑ a, A a=1) :
    ∑ a, naimarkEffect A a=1 := by
  change (∑ a, naimarkSwap A*naimarkOutcome a*naimarkSwap A)=1
  rw [←Finset.sum_mul,←Finset.mul_sum,naimarkOutcome_sum,mul_one]
  exact naimarkSwap_square A hA hAc

theorem stack_projection_compression (A : I → E →L[ℂ] E) (a : I) :
    (blockStack A).adjoint ∘L blockProjection a ∘L blockStack A=(A a).adjoint ∘L A a := by
  have hp : (blockProject (E:=E) a).adjoint=blockInclude a := by
    rw [←blockInclude_adjoint,ContinuousLinearMap.adjoint_adjoint]
  calc
    _=(blockProject a ∘L blockStack A).adjoint ∘L (blockProject a ∘L blockStack A) := by
      simp only [ContinuousLinearMap.adjoint_comp,hp,blockProjection,ContinuousLinearMap.comp_assoc]
    _=_ := by rw [blockStack_component]

theorem naimarkColumn_compression (A : I → E →L[ℂ] E)
    (hA : ∀ a, positiveOperator (A a)) (a : I) :
    (naimarkColumn A).adjoint ∘L naimarkOutcome a ∘L naimarkColumn A=A a := by
  have hs a : (CFC.sqrt (A a)).adjoint=CFC.sqrt (A a) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hsq a : CFC.sqrt (A a) ∘L CFC.sqrt (A a)=A a :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr ((positive_iff _).mp (hA a)))
  by_cases h : a=default <;>
    simp only [naimarkOutcome,h,↓reduceIte,naimarkColumn,
      ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,
      stack_projection_compression,hs,hsq,map_zero,zero_add,add_zero]

theorem naimark_compression (A : I → E →L[ℂ] E)
    (hA : ∀ a, positiveOperator (A a)) (a : I) :
    (naimarkInclusion (I:=I)).adjoint ∘L naimarkEffect A a ∘L naimarkInclusion=A a := by
  have hh := congrArg ContinuousLinearMap.adjoint (naimarkSwap_inclusion A)
  have ht : naimarkInclusion.adjoint ∘L naimarkSwap A=(naimarkColumn A).adjoint := by
    simpa only [ContinuousLinearMap.adjoint_comp,naimarkSwap_adjoint] using hh
  calc
    _=(naimarkInclusion.adjoint ∘L naimarkSwap A) ∘L naimarkOutcome a ∘L
        (naimarkSwap A ∘L naimarkInclusion) := by
      simp only [naimarkEffect,ContinuousLinearMap.comp_assoc]
    _=(naimarkColumn A).adjoint ∘L naimarkOutcome a ∘L naimarkColumn A := by
      rw [ht,naimarkSwap_inclusion]
    _=A a := naimarkColumn_compression A hA a

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.NaimarkSpace
#print axioms Blueprint.SpatialProof.naimarkColumn
#print axioms Blueprint.SpatialProof.naimarkInclusion
#print axioms Blueprint.SpatialProof.naimarkInclusion_gram
#print axioms Blueprint.SpatialProof.naimarkColumn_gram
#print axioms Blueprint.SpatialProof.naimarkInclusion_column
#print axioms Blueprint.SpatialProof.naimarkColumn_inclusion
#print axioms Blueprint.SpatialProof.naimarkSwap
#print axioms Blueprint.SpatialProof.naimarkSwap_adjoint
#print axioms Blueprint.SpatialProof.naimarkSwap_square
#print axioms Blueprint.SpatialProof.naimarkSwap_inclusion
#print axioms Blueprint.SpatialProof.naimarkOutcome
#print axioms Blueprint.SpatialProof.naimarkOutcome_adjoint
#print axioms Blueprint.SpatialProof.naimarkOutcome_square
#print axioms Blueprint.SpatialProof.naimarkOutcome_sum
#print axioms Blueprint.SpatialProof.naimarkEffect
#print axioms Blueprint.SpatialProof.naimarkEffect_adjoint
#print axioms Blueprint.SpatialProof.naimarkEffect_square
#print axioms Blueprint.SpatialProof.naimarkEffect_sum
#print axioms Blueprint.SpatialProof.stack_projection_compression
#print axioms Blueprint.SpatialProof.naimarkColumn_compression
#print axioms Blueprint.SpatialProof.naimark_compression
