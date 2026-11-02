import Blueprint.A.SpatialDilation
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Blueprint.SpatialProof
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev BlockSpace (I E : Type*) := PiLp 2 (fun _ : I => E)

def blockInclude (i : I) : E →L[ℂ] BlockSpace I E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : I => E) i

def blockProject (i : I) : BlockSpace I E →L[ℂ] E := PiLp.proj 2 (fun _ : I => E) i

theorem blockInclude_apply (i j : I) (x : E) :
    (blockInclude i x : BlockSpace I E) j=if j=i then x else 0 := by
  simp [blockInclude,eq_comm]

theorem blockProject_apply (i : I) (x : BlockSpace I E) : blockProject i x=x i := rfl

theorem blockInclude_adjoint (i : I) : (blockInclude (E:=E) i).adjoint=blockProject i := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (x i) y=∑ j, inner ℂ (x j) ((blockInclude i y : BlockSpace I E) j)
  symm
  calc
    _=inner ℂ (x i) ((blockInclude i y : BlockSpace I E) i) :=
      Finset.sum_eq_single i (by intro j hj hji; simp [blockInclude_apply,hji]) (by simp)
    _=_ := by simp [blockInclude_apply]

theorem block_project_include (i j : I) :
    (blockProject (E:=E) i) ∘L blockInclude j=if i=j then 1 else 0 := by
  ext x
  by_cases h : i=j <;> simp [h,blockProject_apply,blockInclude_apply]

def blockProjection (i : I) : BlockSpace I E →L[ℂ] BlockSpace I E :=
  blockInclude i ∘L blockProject i

theorem blockProjection_adjoint (i : I) :
    (blockProjection (E:=E) i).adjoint=blockProjection i := by
  have hp : (blockProject (E:=E) i).adjoint=blockInclude i := by
    rw [←blockInclude_adjoint,ContinuousLinearMap.adjoint_adjoint]
  simp only [blockProjection,ContinuousLinearMap.adjoint_comp,blockInclude_adjoint,hp]

theorem blockProjection_mul (i j : I) :
    blockProjection (E:=E) i*blockProjection j=if i=j then blockProjection i else 0 := by
  change (blockProjection i) ∘L (blockProjection j)=_
  rw [blockProjection,blockProjection,four_comp,block_project_include]
  by_cases h : i=j
  · subst j
    simp [blockProjection,ContinuousLinearMap.one_def]
  · simp [h]

theorem blockProjection_sum : ∑ i : I, blockProjection (E:=E) i=1 := by
  ext x j
  simp [blockProjection,blockInclude,blockProject,WithLp.ofLp_sum]

def blockStack (A : I → E →L[ℂ] E) : E →L[ℂ] BlockSpace I E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi A

theorem blockStack_apply (A : I → E →L[ℂ] E) (x : E) (i : I) : blockStack A x i=A i x := rfl

theorem blockStack_gram (A : I → E →L[ℂ] E) :
    (blockStack A).adjoint ∘L blockStack A=∑ i, (A i).adjoint ∘L A i := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply,blockStack_apply,sum_apply,
    sum_inner,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]

theorem blockStack_component (A : I → E →L[ℂ] E) (i : I) :
    blockProject i ∘L blockStack A=A i := by
  ext x
  rfl

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.BlockSpace
#print axioms Blueprint.SpatialProof.blockInclude
#print axioms Blueprint.SpatialProof.blockProject
#print axioms Blueprint.SpatialProof.blockInclude_apply
#print axioms Blueprint.SpatialProof.blockProject_apply
#print axioms Blueprint.SpatialProof.blockInclude_adjoint
#print axioms Blueprint.SpatialProof.block_project_include
#print axioms Blueprint.SpatialProof.blockProjection
#print axioms Blueprint.SpatialProof.blockProjection_adjoint
#print axioms Blueprint.SpatialProof.blockProjection_mul
#print axioms Blueprint.SpatialProof.blockProjection_sum
#print axioms Blueprint.SpatialProof.blockStack
#print axioms Blueprint.SpatialProof.blockStack_apply
#print axioms Blueprint.SpatialProof.blockStack_gram
#print axioms Blueprint.SpatialProof.blockStack_component
