import Companion.QuantumJensenShannon

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

variable {a : Type*} [Fintype a] [DecidableEq a]

def symmetryProjection (C : Matrix a a ℂ) (s : Bool) : Matrix a a ℂ :=
  (1/2:ℂ) • (1+if s then -C else C)

theorem symmetryProjection_hermitian (C : Matrix a a ℂ) (hC : C.conjTranspose=C) (s : Bool) :
    (symmetryProjection C s).conjTranspose=symmetryProjection C s := by
  cases s <;> simp [symmetryProjection,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hC]

theorem symmetryProjection_square (C : Matrix a a ℂ) (hC : C*C=1) (s : Bool) :
    symmetryProjection C s*symmetryProjection C s=symmetryProjection C s := by
  let D := if s then -C else C
  have hD : D*D=1 := by cases s <;> simp [D,hC]
  have he : (1+D)*(1+D)=(2:ℂ) • (1+D) := by
    simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,Matrix.one_mul,hD]
    module
  change ((1/2:ℂ) • (1+D))*((1/2:ℂ) • (1+D))=(1/2:ℂ) • (1+D)
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,he,smul_smul]
  norm_num

theorem symmetryProjection_positive (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) (s : Bool) :
    (symmetryProjection C s).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (symmetryProjection C s)
  rw [symmetryProjection_hermitian C hC.1 s,symmetryProjection_square C hC.2 s] at h
  exact h

theorem symmetryProjection_complete (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) :
    (∑ s : Bool, (symmetryProjection C s).conjTranspose*symmetryProjection C s)=1 := by
  simp_rw [symmetryProjection_hermitian C hC.1,symmetryProjection_square C hC.2]
  simp only [Fintype.sum_bool,symmetryProjection,Bool.false_eq_true,↓reduceIte]
  module

def pinchingChannel (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) : QIT.Channel a a :=
  krausChannel (symmetryProjection C) (symmetryProjection_complete C hC)

theorem pinchingChannel_map (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) (X : Matrix a a ℂ) :
    (pinchingChannel C hC).map X=(1/2:ℂ) • (X+C*X*C) := by
  change (∑ s : Bool, symmetryProjection C s*X*(symmetryProjection C s).conjTranspose)=_
  simp_rw [symmetryProjection_hermitian C hC.1]
  simp only [Fintype.sum_bool,symmetryProjection,Bool.false_eq_true,↓reduceIte]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_neg,
    Matrix.neg_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
  module

def pinchingState (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) (rho : QIT.State a) : QIT.State a :=
  (pinchingChannel C hC).applyState rho

theorem pinchingState_matrix (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) (rho : QIT.State a) :
    (pinchingState C hC rho).matrix=(1/2:ℂ) • (rho.matrix+C*rho.matrix*C) := pinchingChannel_map C hC _

theorem pinchingState_commute (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) (rho : QIT.State a) :
    Commute (pinchingState C hC rho).matrix C := by
  have h1 : (C*rho.matrix*C)*C=C*rho.matrix := by rw [Matrix.mul_assoc,hC.2,Matrix.mul_one]
  have h2 : C*(C*rho.matrix*C)=rho.matrix*C := by
    calc
      _=(C*C)*(rho.matrix*C) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hC.2,Matrix.one_mul]
  change (pinchingState C hC rho).matrix*C=C*(pinchingState C hC rho).matrix
  rw [pinchingState_matrix]
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,h1,h2]
  rw [add_comm]

theorem trace_pinching_invariant (C : Matrix a a ℂ) (hC : C*C=1) (X H : Matrix a a ℂ)
    (hc : Commute H C) :
    Matrix.trace (((1/2:ℂ) • (X+C*X*C))*H)=Matrix.trace (X*H) := by
  have hCH : C*H*C=H := by
    calc
      _=C*(H*C) := by rw [Matrix.mul_assoc]
      _=C*(C*H) := by rw [hc.eq]
      _=H := by rw [← Matrix.mul_assoc,hC,Matrix.one_mul]
  have ht : Matrix.trace ((C*X*C)*H)=Matrix.trace (X*H) := by
    calc
      _=Matrix.trace (C*((X*C)*H)) := by simp only [Matrix.mul_assoc]
      _=Matrix.trace (((X*C)*H)*C) := Matrix.trace_mul_comm _ _
      _=Matrix.trace (X*(C*H*C)) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hCH]
  rw [Matrix.smul_mul,Matrix.trace_smul,Matrix.add_mul,Matrix.trace_add,ht]
  simp only [smul_eq_mul]
  ring

end
end Companion.Analytic.CountProof
