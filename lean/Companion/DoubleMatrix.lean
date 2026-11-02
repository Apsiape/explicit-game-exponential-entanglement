import Companion.GadgetEstimates
set_option maxHeartbeats 100000

namespace Companion.DoubleMatrix
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
open Analytic
variable {α : Type} [Fintype α] [DecidableEq α]
abbrev U (α : Type) [Fintype α] [DecidableEq α] := Matrix.unitaryGroup α ℂ

def matrix (sw : Bool) (A B : Matrix α α ℂ) : Matrix (Bool × α) (Bool × α) ℂ :=
  fun (r,i) (s,j) => if s=(r ^^ sw) then (if r then B else A) i j else 0

theorem matrix_mul (sw tw : Bool) (A B C D : Matrix α α ℂ) :
    matrix sw A B*matrix tw C D=
      matrix (sw ^^ tw) (A*(if sw then D else C)) (B*(if sw then C else D)) := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> cases sw <;> cases tw
  all_goals simp [matrix,Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_bool]

theorem matrix_star (sw : Bool) (A B : Matrix α α ℂ) :
    (matrix sw A B).conjTranspose=
      matrix sw (if sw then B.conjTranspose else A.conjTranspose)
        (if sw then A.conjTranspose else B.conjTranspose) := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> cases sw <;> simp [matrix,Matrix.conjTranspose_apply]

theorem matrix_one : matrix false (1 : Matrix α α ℂ) 1=1 := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> simp [matrix,Matrix.one_apply,Prod.mk.injEq]

def mono (sw : Bool) (A B : U α) : U (Bool × α) :=
  ⟨matrix sw (A:Matrix α α ℂ) (B:Matrix α α ℂ),by
    change (matrix sw (A:Matrix α α ℂ) (B:Matrix α α ℂ)).conjTranspose*
        matrix sw (A:Matrix α α ℂ) (B:Matrix α α ℂ)=1 ∧
      matrix sw (A:Matrix α α ℂ) (B:Matrix α α ℂ)*
        (matrix sw (A:Matrix α α ℂ) (B:Matrix α α ℂ)).conjTranspose=1
    rw [matrix_star,matrix_mul,matrix_mul]
    have ha1 : (A:Matrix α α ℂ).conjTranspose*A=1 := A.property.1
    have ha2 : (A:Matrix α α ℂ)*(A:Matrix α α ℂ).conjTranspose=1 := A.property.2
    have hb1 : (B:Matrix α α ℂ).conjTranspose*B=1 := B.property.1
    have hb2 : (B:Matrix α α ℂ)*(B:Matrix α α ℂ).conjTranspose=1 := B.property.2
    cases sw <;> simp [ha1,ha2,hb1,hb2,matrix_one]⟩

theorem mono_mul (sw tw : Bool) (A B C D : U α) :
    mono sw A B*mono tw C D=
      mono (sw ^^ tw) (A*(if sw then D else C)) (B*(if sw then C else D)) := by
  apply Subtype.ext
  cases sw <;> cases tw <;> exact matrix_mul _ _ _ _ _ _

theorem mono_inv (sw : Bool) (A B : U α) :
    (mono sw A B)⁻¹=mono sw (if sw then B⁻¹ else A⁻¹) (if sw then A⁻¹ else B⁻¹) := by
  apply Subtype.ext
  cases sw <;> exact matrix_star _ _ _

theorem mono_one : mono false (1 : U α) 1=1 := Subtype.ext matrix_one
abbrev diag (A B : U α) := mono false A B
abbrev anti (A B : U α) := mono true A B
abbrev swap (α : Type) [Fintype α] [DecidableEq α] : U (Bool × α) := anti (1 : U α) 1

def copy : U α →* U (Bool × α) where
  toFun A := diag A A
  map_one' := mono_one
  map_mul' A B := (mono_mul false false A A B B).symm
def first : U α →* U (Bool × α) where
  toFun A := diag A 1
  map_one' := mono_one
  map_mul' A B := by simpa using (mono_mul false false A 1 B 1).symm

def sizeNorm (A : Matrix α α ℂ) : ℝ := hsNorm A/Real.sqrt (Fintype.card α : ℝ)
def defect (A : U α) : ℝ := sizeNorm ((A:Matrix α α ℂ)-1)

theorem sizeNorm_nonneg (A : Matrix α α ℂ) : 0≤sizeNorm A :=
  div_nonneg (hsNorm_nonneg _) (Real.sqrt_nonneg _)
theorem defect_nonneg (A : U α) : 0≤defect A := sizeNorm_nonneg _
theorem defect_one : defect (1 : U α)=0 := by simp [defect,sizeNorm,hsNorm_eq_frobenius]

def length : InvariantLength (U α) where
  value := defect
  nonneg := defect_nonneg
  one := defect_one
  mul_le A B := by
    have he : ((A*B:U α):Matrix α α ℂ)-1=(A:Matrix α α ℂ)*((B:Matrix α α ℂ)-1)+((A:Matrix α α ℂ)-1) := by
      simp only [Submonoid.coe_mul,Matrix.mul_sub,Matrix.mul_one,sub_add_sub_cancel]
    unfold defect sizeNorm
    rw [he]
    have h := hsNorm_add_le ((A:Matrix α α ℂ)*((B:Matrix α α ℂ)-1)) ((A:Matrix α α ℂ)-1)
    rw [hsNorm_unitary_left _ _ A.property.1] at h
    simpa [add_div,add_comm] using div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)
  inv A := by
    have ha2 : (A:Matrix α α ℂ)*(A:Matrix α α ℂ).conjTranspose=1 := A.property.2
    have he : ((A⁻¹:U α):Matrix α α ℂ)-1=(A:Matrix α α ℂ).conjTranspose*(1-(A:Matrix α α ℂ)) := by
      change (A:Matrix α α ℂ).conjTranspose-1=_
      have ha : (A:Matrix α α ℂ).conjTranspose*A=1 := A.property.1
      rw [Matrix.mul_sub,Matrix.mul_one,ha]
    unfold defect sizeNorm
    rw [he,hsNorm_unitary_left _ _ (by simpa only [Matrix.conjTranspose_conjTranspose] using ha2)]
    simp only [hsNorm_eq_frobenius,norm_sub_rev]
  conjugate A B := by
    have ha1 : (A:Matrix α α ℂ).conjTranspose*(A:Matrix α α ℂ)=1 := A.property.1
    have he : ((A*B*A⁻¹:U α):Matrix α α ℂ)-1=
        (A:Matrix α α ℂ)*((B:Matrix α α ℂ)-1)*(A:Matrix α α ℂ).conjTranspose := by
      change (A:Matrix α α ℂ)*B*(A:Matrix α α ℂ).conjTranspose-1=_
      have ha : (A:Matrix α α ℂ)*(A:Matrix α α ℂ).conjTranspose=1 := A.property.2
      rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,ha]
    unfold defect sizeNorm
    rw [he,hsNorm_unitary_right _ _ (by simpa only [Matrix.conjTranspose_conjTranspose] using ha1),
      hsNorm_unitary_left _ _ A.property.1]

theorem matrix_diag (A B : Matrix α α ℂ) : matrix false A B=diagonalBlocks A B := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> rfl

theorem diagonal_bound (hcard : 0<Fintype.card α) (A B : U α) (eps : ℝ) (heps : 0≤eps)
    (hA : defect A≤eps) (hB : defect B≤eps) : defect (diag A B)≤eps := by
  have hs : 0<Real.sqrt (Fintype.card α:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hcard)
  have ht : 0<Real.sqrt (2*(Fintype.card α:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hA' : hsNorm ((A:Matrix α α ℂ)-1)≤eps*Real.sqrt (Fintype.card α:ℝ) := (div_le_iff₀ hs).mp hA
  have hB' : hsNorm ((B:Matrix α α ℂ)-1)≤eps*Real.sqrt (Fintype.card α:ℝ) := (div_le_iff₀ hs).mp hB
  change hsNorm (matrix false (A:Matrix α α ℂ) (B:Matrix α α ℂ)-1)/Real.sqrt (Fintype.card (Bool × α):ℝ)≤eps
  rw [matrix_diag,diagonalBlocks_sub_one]
  simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
  apply (div_le_iff₀ ht).mpr
  apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg heps ht.le)).mp
  rw [hsNorm_sq,hsSquared_diagonalBlocks]
  have hAs := (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg heps hs.le)).mpr hA'
  have hBs := (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg heps hs.le)).mpr hB'
  rw [hsNorm_sq] at hAs hBs
  simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (show (0:ℝ)≤2*Fintype.card α by positivity)] at *
  nlinarith

theorem diagonal_first (hcard : 0<Fintype.card α) (A : U α) :
    defect (diag A 1)=defect A/Real.sqrt 2 := by
  unfold defect sizeNorm
  change hsNorm (matrix false (A:Matrix α α ℂ) (1:Matrix α α ℂ)-1)/Real.sqrt (Fintype.card (Bool × α):ℝ)=_
  rw [matrix_diag,diagonalBlocks_sub_one]
  have he : hsNorm (diagonalBlocks ((A:Matrix α α ℂ)-1) 0)=hsNorm ((A:Matrix α α ℂ)-1) := by
    unfold hsNorm
    rw [hsSquared_diagonalBlocks]
    simp [hsSquared]
  simp only [sub_self] at *
  rw [he]
  simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end
end Companion.DoubleMatrix
