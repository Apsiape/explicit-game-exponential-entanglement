import Companion.DoubleMatrix
import Companion.StageBlocks

namespace Companion.BlockExtension
noncomputable section
open DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

def value (phi : FreeGroup Nat →* U α) (b : WordBlock) : U (Bool × α) :=
  mono b.swapped (phi (FreeGroup.mk b.first)) (phi (FreeGroup.mk b.second))

theorem value_mul (phi : FreeGroup Nat →* U α) (a b : WordBlock) :
    value phi (blockMul a b)=value phi a*value phi b := by
  unfold value
  rw [mono_mul]
  cases h : a.swapped <;> simp [blockMul,h,← FreeGroup.mul_mk,map_mul]

theorem value_inv (phi : FreeGroup Nat →* U α) (a : WordBlock) :
    value phi (blockInv a)=(value phi a)⁻¹ := by
  unfold value
  rw [mono_inv]
  cases h : a.swapped <;> simp [blockInv,h,← FreeGroup.inv_mk,map_inv]

theorem value_one (phi : FreeGroup Nat →* U α) : value phi ⟨false,[],[]⟩=1 := by
  simp [value,← FreeGroup.one_eq_mk,mono_one]

def blockAt (assignments : List WordBlock) (j : Nat) : WordBlock := assignments[j-1]?.getD ⟨false,[],[]⟩
def step (assignments : List WordBlock) (a : Nat × Bool) : WordBlock :=
  if a.2 then blockAt assignments a.1 else blockInv (blockAt assignments a.1)
def unitStep (phi : FreeGroup Nat →* U α) (assignments : List WordBlock) (a : Nat × Bool) : U (Bool × α) :=
  if a.2 then value phi (blockAt assignments a.1) else (value phi (blockAt assignments a.1))⁻¹
def hom (phi : FreeGroup Nat →* U α) (assignments : List WordBlock) : FreeGroup Nat →* U (Bool × α) :=
  FreeGroup.lift (fun j => value phi (blockAt assignments j))

theorem value_step (phi : FreeGroup Nat →* U α) (assignments : List WordBlock) (a : Nat × Bool) :
    value phi (step assignments a)=unitStep phi assignments a := by
  cases h : a.2 <;> simp [step,unitStep,h,value_inv]

theorem fold_value (phi : FreeGroup Nat →* U α) (assignments : List WordBlock) (w : Word) (b : WordBlock) :
    value phi (w.foldl (fun v a => blockMul v (step assignments a)) b)=
      value phi b*(w.map (unitStep phi assignments)).prod := by
  induction w generalizing b with
  | nil => simp
  | cons a w ih =>
    rw [List.foldl_cons,ih,value_mul,value_step]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

theorem hom_word (phi : FreeGroup Nat →* U α) (assignments : List WordBlock) (w : Word) :
    hom phi assignments (FreeGroup.mk w)=value phi (StageBlocks.evalWith assignments w) := by
  have h := fold_value phi assignments w ⟨false,[],[]⟩
  rw [value_one,one_mul] at h
  rw [hom,FreeGroup.lift_mk]
  simp only [Bool.cond_eq_ite]
  change (w.map (unitStep phi assignments)).prod=value phi (StageBlocks.evalWith assignments w)
  exact h.symm

theorem bound (hcard : 0<Fintype.card α) (phi : FreeGroup Nat →* U α)
    (assignments : List WordBlock) (relators : List Word) (R : RelKey → Option Word) (k : Nat)
    (hdiag : relators.all (fun w => !(StageBlocks.evalWith assignments w).swapped)=true)
    (hareas : ∀ w ∈ StageBlocks.blockWords assignments relators, HasAreaWith R w k)
    (eps : ℝ) (heps : 0≤eps)
    (hr : ∀ i r, R i=some r → defect (phi (FreeGroup.mk r))≤eps) :
    ∀ r ∈ relators, defect (hom phi assignments (FreeGroup.mk r))≤k*eps := by
  intro r hmem
  rw [hom_word]
  have hs : (StageBlocks.evalWith assignments r).swapped=false := by
    have h := List.all_eq_true.mp hdiag r hmem
    simpa using h
  unfold value
  rw [hs]
  apply diagonal_bound hcard _ _ (k*eps) (by positivity)
  · apply (hareas _ (List.mem_flatMap.mpr ⟨r,hmem,by simp⟩)).length_bound
      (DoubleMatrix.length (α:=α)) phi eps heps hr
  · apply (hareas _ (List.mem_flatMap.mpr ⟨r,hmem,by simp⟩)).length_bound
      (DoubleMatrix.length (α:=α)) phi eps heps hr

theorem stage1_bound (hcard : 0<Fintype.card α) (phi : FreeGroup Nat →* U α) (eps : ℝ) (heps : 0≤eps)
    (hr : ∀ i r, StageBlocks.stage1Base i=some r → defect (phi (FreeGroup.mk r))≤eps) :
    ∀ r ∈ StageBlocks.stage1Relators, defect (hom phi StageBlocks.stage1Assignments (FreeGroup.mk r))≤eps := by
  simpa using bound hcard phi _ _ _ 1 StageBlocks.stage1_diagonal StageBlocks.stage1_areas eps heps hr
theorem stage3_bound (hcard : 0<Fintype.card α) (phi : FreeGroup Nat →* U α) (eps : ℝ) (heps : 0≤eps)
    (hr : ∀ i r, StageBlocks.stage3Base i=some r → defect (phi (FreeGroup.mk r))≤eps) :
    ∀ r ∈ StageBlocks.stage3Relators, defect (hom phi StageBlocks.stage3Assignments (FreeGroup.mk r))≤eps := by
  simpa using bound hcard phi _ _ _ 1 StageBlocks.stage3_diagonal StageBlocks.stage3_areas eps heps hr
theorem stage4_bound (hcard : 0<Fintype.card α) (phi : FreeGroup Nat →* U α) (eps : ℝ) (heps : 0≤eps)
    (hr : ∀ i r, StageBlocks.stage4Base i=some r → defect (phi (FreeGroup.mk r))≤eps) :
    ∀ r ∈ StageBlocks.stage4Relators, defect (hom phi StageBlocks.stage4Assignments (FreeGroup.mk r))≤3*eps :=
  bound hcard phi _ _ _ 3 StageBlocks.stage4_diagonal StageBlocks.stage4_areas eps heps hr

end
end Companion.BlockExtension
