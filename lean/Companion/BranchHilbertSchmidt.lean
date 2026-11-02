import Companion.RoundedParityBounds

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

def stackMatrices {z : Type*} {d n : Nat} (A : z → Matrix (Fin d) (Fin n) ℂ) :
    Matrix (z × Fin d) (Fin n) ℂ := fun zi j => A zi.1 zi.2 j

def familyHS {z : Type*} [Fintype z] {d n : Nat} (A : z → Matrix (Fin d) (Fin n) ℂ) : ℝ :=
  hsNorm (stackMatrices A)

theorem familyHS_nonneg {z : Type*} [Fintype z] {d n : Nat} (A : z → Matrix (Fin d) (Fin n) ℂ) :
    0≤familyHS A := hsNorm_nonneg _

theorem familyHS_sq {z : Type*} [Fintype z] {d n : Nat} (A : z → Matrix (Fin d) (Fin n) ℂ) :
    familyHS A^2=∑ a, hsNorm (A a)^2 := by
  simp only [familyHS,hsNorm_sq,hsSquared,stackMatrices,Fintype.sum_prod_type]

theorem familyHS_add {z : Type*} [Fintype z] {d n : Nat} (A B : z → Matrix (Fin d) (Fin n) ℂ) :
    familyHS (fun a => A a+B a)≤familyHS A+familyHS B :=
  hsNorm_add_le (stackMatrices A) (stackMatrices B)

theorem hsNorm_sq_columns {d n : Nat} (A : Matrix (Fin d) (Fin n) ℂ) :
    hsNorm A^2=∑ j, ‖CountProof.columnVector A j‖^2 := by
  simp only [CountProof.columnVector_norm_sq,hsNorm_sq,hsSquared_trace,Matrix.trace,Complex.re_sum,Matrix.diag_apply]

/-- Left multiplication is bounded in HS norm by the actual operator
norm of C, rather than its Frobenius norm. -/
theorem operator_mul_hs_bound {d n : Nat} (C : Mat d) (A : Matrix (Fin d) (Fin n) ℂ) :
    hsNorm (C*A)≤‖C‖*hsNorm A := by
  have hcol (j : Fin n) : CountProof.columnVector (C*A) j=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℂ) C (CountProof.columnVector A j) := by
    ext i
    rfl
  have hj (j : Fin n) : ‖CountProof.columnVector (C*A) j‖≤‖C‖*‖CountProof.columnVector A j‖ := by
    rw [hcol,Matrix.cstar_norm_def]
    exact (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℂ) C).le_opNorm _
  have hsq : hsNorm (C*A)^2≤(‖C‖*hsNorm A)^2 := by
    rw [hsNorm_sq_columns]
    calc
      _≤∑ j, (‖C‖*‖CountProof.columnVector A j‖)^2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hj j) 2)
      _=‖C‖^2*(∑ j, ‖CountProof.columnVector A j‖^2) := by simp only [mul_pow,Finset.mul_sum]
      _=(‖C‖*hsNorm A)^2 := by rw [← hsNorm_sq_columns]; ring
  exact (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (norm_nonneg _) (hsNorm_nonneg _))).mp hsq

theorem familyHS_left_mul_bound {z : Type*} [Fintype z] {d n : Nat}
    (C : Mat d) (A : z → Matrix (Fin d) (Fin n) ℂ) :
    familyHS (fun a => C*A a)≤‖C‖*familyHS A := by
  have hsq : familyHS (fun a => C*A a)^2≤(‖C‖*familyHS A)^2 := by
    rw [familyHS_sq]
    calc
      _≤∑ a, (‖C‖*hsNorm (A a))^2 :=
        Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (hsNorm_nonneg _) (operator_mul_hs_bound C (A a)) 2)
      _=‖C‖^2*(∑ a, hsNorm (A a)^2) := by simp only [mul_pow,Finset.mul_sum]
      _=_ := by rw [← familyHS_sq]; ring
  exact (sq_le_sq₀ (familyHS_nonneg _) (mul_nonneg (norm_nonneg _) (familyHS_nonneg _))).mp hsq

theorem familyHS_right_parseval {z : Type*} [Fintype z] {d : Nat}
    (K : z → Mat d) (hK : ∑ a, K a*(K a).conjTranspose=1) (A : Mat d) :
    familyHS (fun a => A*K a)=hsNorm A := by
  have hcomp : ∑ a, ((K a).conjTranspose).conjTranspose*(K a).conjTranspose=1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hK
  have h := CountProof.measurement_parseval (fun a => (K a).conjTranspose) hcomp A.conjTranspose
  have he (a : z) : hsNorm ((K a).conjTranspose*A.conjTranspose)=hsNorm (A*K a) := by
    rw [← Matrix.conjTranspose_mul,hsNorm_conjTranspose]
  simp only [he,hsNorm_conjTranspose] at h
  have hs : familyHS (fun a => A*K a)^2=hsNorm A^2 := by rw [familyHS_sq,h]
  exact (sq_eq_sq₀ (familyHS_nonneg _) (hsNorm_nonneg _)).mp hs

/-- The general branch estimate of the sequential-measurement argument:
the operator norm multiplies the total branch commutator error. -/
theorem branch_weight_bound {z : Type*} [Fintype z] {d : Nat}
    (K : z → Mat d) (hK : ∑ a, K a*(K a).conjTranspose=1) (eta C : Mat d) :
    familyHS (fun a => C*K a*eta)≤hsNorm (C*eta)+‖C‖*familyHS (fun a => comm (K a) eta) := by
  have he : (fun a => C*K a*eta)=(fun a => (C*eta)*K a+C*comm (K a) eta) := by
    funext a
    simp only [comm,Matrix.mul_sub,Matrix.mul_assoc]
    abel
  rw [he]
  have h := familyHS_add (fun a => (C*eta)*K a) (fun a => C*comm (K a) eta)
  rw [familyHS_right_parseval K hK (C*eta)] at h
  have hb := familyHS_left_mul_bound C (fun a => comm (K a) eta)
  linarith

/-- Sequential projector words have both completeness identities, without
any commutation assumption on the measured involutions. -/
theorem jointProjection_coComplete {d : Nat} (n : Nat) (C : Fin n → Mat d)
    (hC : ∀ i, IsInvolution (C i)) :
    (∑ a, CountProof.jointProjection n C a*(CountProof.jointProjection n C a).conjTranspose)=1 := by
  induction n with
  | zero => simp [CountProof.jointProjection]
  | succ n ih =>
    rw [sum_cube_succ,Finset.sum_comm]
    have hP : (∑ b : Bool, CountProof.symmetryProjection (C 0) b*(CountProof.symmetryProjection (C 0) b).conjTranspose)=1 := by
      simpa only [CountProof.symmetryProjection_hermitian _ (hC 0).1] using CountProof.symmetryProjection_complete (C 0) (hC 0)
    have he (a : Fin n → Bool) :
        (∑ b : Bool, CountProof.jointProjection (n+1) C (Fin.cons b a)*
          (CountProof.jointProjection (n+1) C (Fin.cons b a)).conjTranspose)=
        CountProof.jointProjection n (Fin.tail C) a*(CountProof.jointProjection n (Fin.tail C) a).conjTranspose := by
      simp only [CountProof.jointProjection,Fin.tail_cons,Fin.cons_zero,Matrix.conjTranspose_mul]
      calc
        _=CountProof.jointProjection n (Fin.tail C) a*
            (∑ b : Bool, CountProof.symmetryProjection (C 0) b*(CountProof.symmetryProjection (C 0) b).conjTranspose)*
              (CountProof.jointProjection n (Fin.tail C) a).conjTranspose := by
          simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
        _=_ := by rw [hP,Matrix.mul_one]
    simp_rw [he]
    exact ih (Fin.tail C) (fun i => hC i.succ)

theorem sequential_branch_weight_bound {d : Nat} (n : Nat) (Q : Fin n → Mat d)
    (hQ : ∀ i, IsInvolution (Q i)) (eta C : Mat d) :
    familyHS (fun a => C*CountProof.jointProjection n Q a*eta)≤hsNorm (C*eta)+
      ‖C‖*familyHS (fun a => comm (CountProof.jointProjection n Q a) eta) :=
  branch_weight_bound _ (jointProjection_coComplete n Q hQ) eta C

end
end Companion.Analytic.ReturnProof
