import Companion.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.TensorProduct
set_option maxHeartbeats 400000

namespace Companion.Analytic
noncomputable section
open scoped TensorProduct BigOperators Matrix.Norms.Frobenius ComplexOrder

abbrev LocalSpace (d : Nat) := EuclideanSpace ℂ (Fin d)
abbrev JointSpace (dA dB : Nat) := LocalSpace dA ⊗[ℂ] LocalSpace dB

def jointBasis (dA dB : Nat) :=
  (EuclideanSpace.basisFun (Fin dA) ℂ).tensorProduct (EuclideanSpace.basisFun (Fin dB) ℂ)

/-- The actual Hilbert tensor-product vector is represented by its Bob-row,
Alice-column coefficient matrix. This fixes the transpose convention. -/
def thetaTensor {dA dB : Nat} (psi : JointSpace dA dB) : Matrix (Fin dB) (Fin dA) ℂ :=
  fun b a => (jointBasis dA dB).repr psi (a,b)

def thetaTensorInv {dA dB : Nat} (A : Matrix (Fin dB) (Fin dA) ℂ) : JointSpace dA dB :=
  (jointBasis dA dB).repr.symm (WithLp.toLp 2 (fun ab => A ab.2 ab.1))

theorem thetaTensor_left_inv {dA dB : Nat} (psi : JointSpace dA dB) :
    thetaTensorInv (thetaTensor psi)=psi := by
  apply (jointBasis dA dB).repr.injective
  ext ab
  simp [thetaTensorInv,thetaTensor]

theorem thetaTensor_right_inv {dA dB : Nat} (A : Matrix (Fin dB) (Fin dA) ℂ) :
    thetaTensor (thetaTensorInv A)=A := by
  ext b a
  simp [thetaTensorInv,thetaTensor]

theorem thetaTensor_zero {dA dB : Nat} : thetaTensor (0 : JointSpace dA dB)=0 := by
  ext b a; simp [thetaTensor]

theorem thetaTensor_add {dA dB : Nat} (psi chi : JointSpace dA dB) :
    thetaTensor (psi+chi)=thetaTensor psi+thetaTensor chi := by
  ext b a; simp [thetaTensor]

theorem thetaTensor_smul {dA dB : Nat} (c : ℂ) (psi : JointSpace dA dB) :
    thetaTensor (c • psi)=c • thetaTensor psi := by
  ext b a; simp [thetaTensor]

/-- A linear equivalence, rather than only a convention for pure tensors. -/
def thetaTensorEquiv (dA dB : Nat) :
    JointSpace dA dB ≃ₗ[ℂ] Matrix (Fin dB) (Fin dA) ℂ where
  toFun := thetaTensor
  invFun := thetaTensorInv
  left_inv := thetaTensor_left_inv
  right_inv := thetaTensor_right_inv
  map_add' := thetaTensor_add
  map_smul' := thetaTensor_smul

theorem thetaTensor_inner {dA dB : Nat} (psi chi : JointSpace dA dB) :
    inner ℂ psi chi = ∑ b, ∑ a, star (thetaTensor psi b a)*thetaTensor chi b a := by
  rw [← (jointBasis dA dB).repr.inner_map_map psi chi]
  simp only [PiLp.inner_apply,Fintype.sum_prod_type,RCLike.inner_apply,thetaTensor]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem thetaTensor_norm {dA dB : Nat} (psi : JointSpace dA dB) : hs (thetaTensor psi)=‖psi‖ := by
  rw [hs_eq_hsNorm,hsNorm]
  have he : hsSquared (thetaTensor psi)=‖psi‖^2 := by
    rw [← (jointBasis dA dB).repr.norm_map psi,EuclideanSpace.norm_sq_eq]
    simp only [hsSquared,thetaTensor,Fintype.sum_prod_type,Complex.normSq_eq_norm_sq]
    exact Finset.sum_comm
  rw [he,Real.sqrt_sq (norm_nonneg _)]

def matrixOperator {d : Nat} (A : Mat d) : LocalSpace d →ₗ[ℂ] LocalSpace d := Matrix.toLpLin 2 2 A

def tensorOperator {dA dB : Nat} (P : Mat dA) (Q : Mat dB) :
    JointSpace dA dB →ₗ[ℂ] JointSpace dA dB := TensorProduct.map (matrixOperator P) (matrixOperator Q)

theorem thetaTensor_tmul {dA dB : Nat} (x : LocalSpace dA) (y : LocalSpace dB) (b : Fin dB) (a : Fin dA) :
    thetaTensor (x ⊗ₜ[ℂ] y) b a=y b*x a := by
  simp [thetaTensor,jointBasis]

/-- Both local operators act exactly as asserted in the paper's standard
form: Alice on the right by the transpose, Bob on the left. -/
theorem thetaTensor_operators {dA dB : Nat} (P : Mat dA) (Q : Mat dB) (psi : JointSpace dA dB) :
    thetaTensor (tensorOperator P Q psi)=Q*thetaTensor psi*P.transpose := by
  induction psi using TensorProduct.induction_on with
  | zero => simp [thetaTensor_zero]
  | tmul x y =>
    ext b a
    simp only [tensorOperator,matrixOperator,TensorProduct.map_tmul,thetaTensor_tmul,
      Matrix.toLpLin_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.mulVec,dotProduct,
      Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm]
    exact Finset.sum_comm
  | add psi chi ih1 ih2 =>
    simp [thetaTensor_add,ih1,ih2,Matrix.mul_add,Matrix.add_mul]

theorem expectation_tensor {dA dB : Nat} (psi : JointSpace dA dB) (P : Mat dA) (Q : Mat dB) :
    expectation (thetaTensor psi) P Q=(inner ℂ psi (tensorOperator P Q psi)).re := by
  rw [thetaTensor_inner,thetaTensor_operators]
  rfl

def canonicalPurification {d : Nat} (s : State d) : JointSpace d d := thetaTensorInv s.xi

theorem canonicalPurification_coefficients {d : Nat} (s : State d) :
    thetaTensor (canonicalPurification s)=s.xi := thetaTensor_right_inv _

theorem canonicalPurification_norm {d : Nat} (s : State d) : ‖canonicalPurification s‖=1 := by
  rw [← thetaTensor_norm,canonicalPurification_coefficients,hs_eq_hsNorm,hsNorm]
  have he : hsSquared s.xi=1 := by
    rw [hsSquared_trace,s.xi_positive.isHermitian.eq,s.xi_square,s.normalized]
    rfl
  rw [he,Real.sqrt_one]

/-- The canonical-purification mimic identity, including its state commutator. -/
theorem canonicalPurification_mimic {d : Nat} (s : State d) (B : Mat d) :
    ‖tensorOperator B.transpose 1 (canonicalPurification s)-
      tensorOperator 1 B (canonicalPurification s)‖=hs (comm B s.xi) := by
  rw [← thetaTensor_norm]
  have hsub {a b : Nat} (x y : JointSpace a b) : thetaTensor (x-y)=thetaTensor x-thetaTensor y :=
    (thetaTensorEquiv a b).map_sub x y
  rw [hsub,thetaTensor_operators,thetaTensor_operators,canonicalPurification_coefficients]
  simp only [Matrix.one_mul,Matrix.mul_one,Matrix.transpose_transpose,Matrix.transpose_one]
  rw [show s.xi*B-B*s.xi=-(comm B s.xi) by simp only [comm,neg_sub]]
  simp only [hs_eq_hsNorm,hsNorm_eq_frobenius,norm_neg]

end
end Companion.Analytic
