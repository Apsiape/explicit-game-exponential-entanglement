import Companion.BlockExtension

namespace Companion.StageValues
noncomputable section
open DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

def tripleHom (A B C : U α) : FreeGroup Nat →* U α :=
  FreeGroup.lift (fun j => if j=1 then A else if j=2 then B else if j=3 then C else 1)
def stage1 (B C Y : U α) := BlockExtension.hom (tripleHom B C Y) StageBlocks.stage1Assignments
def stage3 (A B C : U α) := BlockExtension.hom (tripleHom A B C) StageBlocks.stage3Assignments
def stage4 (A B C : U α) := BlockExtension.hom (tripleHom A B C) StageBlocks.stage4Assignments

def values1 (B C Y : U α) : List (U (Bool × α)) :=
  [diag B 1,diag C 1,swap α,anti Y⁻¹ Y,diag 1 (Y*B*Y⁻¹)]
def values3 (A B C : U α) : List (U (Bool × α)) :=
  [diag A A,diag B B,diag C C,swap α,anti A A,diag A 1,diag 1 A,
    diag B 1,diag 1 B,diag C 1,diag 1 C,diag B C,diag C B]
def values4 (A B C : U α) : List (U (Bool × α)) :=
  [diag A A,diag B B,diag C C,anti A A,swap α,anti B B,
    anti (B*A) (A*B),diag (B*A*B) A,diag (B*C) 1,diag B C]

theorem value1 (B C Y : U α) (i : Fin 5) : stage1 B C Y (FreeGroup.of (i.val+1))=(values1 B C Y)[i.val] := by
  fin_cases i <;> simp [stage1,BlockExtension.hom,BlockExtension.blockAt,BlockExtension.value,
    StageBlocks.stage1Assignments,tripleHom,FreeGroup.lift_mk,values1,mul_assoc]
theorem value3 (A B C : U α) (i : Fin 13) : stage3 A B C (FreeGroup.of (i.val+1))=(values3 A B C)[i.val] := by
  fin_cases i <;> simp [stage3,BlockExtension.hom,BlockExtension.blockAt,BlockExtension.value,
    StageBlocks.stage3Assignments,tripleHom,FreeGroup.lift_mk,values3]
theorem value4 (A B C : U α) (i : Fin 10) : stage4 A B C (FreeGroup.of (i.val+1))=(values4 A B C)[i.val] := by
  fin_cases i <;> simp [stage4,BlockExtension.hom,BlockExtension.blockAt,BlockExtension.value,
    StageBlocks.stage4Assignments,tripleHom,FreeGroup.lift_mk,values4,mul_assoc]

theorem bounds1 (hc : 0<Fintype.card α) (B C Y : U α) (eps : ℝ) (he : 0≤eps)
    (hB : defect (B*B)≤eps) (hC : defect (C*C)≤eps) (hy : defect (Y*B*Y⁻¹*C⁻¹)≤eps) :
    ∀ r ∈ StageBlocks.stage1Relators, defect (stage1 B C Y (FreeGroup.mk r))≤eps := by
  apply BlockExtension.stage1_bound hc _ eps he
  intro k r hr
  cases k with
  | square j => rcases j with _|_|j <;> simp_all [StageBlocks.stage1Base] <;> subst r <;>
      simp_all [tripleHom,FreeGroup.lift_mk,mul_assoc]
  | conjugacy j => cases j <;> simp_all [StageBlocks.stage1Base] <;> subst r <;>
      simp_all [tripleHom,FreeGroup.lift_mk,mul_assoc]
  | _ => simp [StageBlocks.stage1Base] at hr

theorem bounds3 (hc : 0<Fintype.card α) (A B C : U α) (eps : ℝ) (he : 0≤eps)
    (hA : defect (A*A)≤eps) (hB : defect (B*B)≤eps) (hC : defect (C*C)≤eps)
    (ht : defect (A*B*A*C⁻¹)≤eps) :
    ∀ r ∈ StageBlocks.stage3Relators, defect (stage3 A B C (FreeGroup.mk r))≤eps := by
  apply BlockExtension.stage3_bound hc _ eps he
  intro k r hr
  cases k with
  | square j => rcases j with _|_|_|j <;> simp_all [StageBlocks.stage3Base] <;> subst r <;>
      simp_all [tripleHom,FreeGroup.lift_mk,mul_assoc]
  | conjugacy j => cases j <;> simp_all [StageBlocks.stage3Base] <;> subst r <;>
      simp_all [tripleHom,FreeGroup.lift_mk,mul_assoc]
  | _ => simp [StageBlocks.stage3Base] at hr

theorem bounds4 (hc : 0<Fintype.card α) (A B C : U α) (eps : ℝ) (he : 0≤eps)
    (hA : defect (A*A)≤eps) (hB : defect (B*B)≤eps) (hC : defect (C*C)≤eps)
    (ht : defect (A*B*A*C⁻¹)≤eps) (hcomm : defect (B*C*B⁻¹*C⁻¹)≤eps) :
    ∀ r ∈ StageBlocks.stage4Relators, defect (stage4 A B C (FreeGroup.mk r))≤3*eps := by
  apply BlockExtension.stage4_bound hc _ eps he
  intro k r hr
  cases k with
  | square j => rcases j with _|_|_|j <;> simp_all [StageBlocks.stage4Base] <;> subst r <;>
      simp_all [tripleHom,FreeGroup.lift_mk,mul_assoc]
  | conjugacy j => rcases j with _|_|j <;> simp_all [StageBlocks.stage4Base] <;> subst r <;>
      simp_all [tripleHom,FreeGroup.lift_mk,mul_assoc]
  | _ => simp [StageBlocks.stage4Base] at hr

end
end Companion.StageValues
