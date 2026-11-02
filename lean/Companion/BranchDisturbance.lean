import Companion.SequentialBranchBounds

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 600000

theorem familyHS_sub_le {a : Type*} [Fintype a] {d : Nat} (A B : a → Mat d) :
    familyHS (fun a => A a-B a)≤familyHS A+familyHS B := by
  change hsNorm (stackMatrices A-stackMatrices B)≤hsNorm (stackMatrices A)+hsNorm (stackMatrices B)
  simpa only [hsNorm_eq_frobenius] using norm_sub_le (stackMatrices A) (stackMatrices B)

theorem familyHS_left_unitary {a : Type*} [Fintype a] {d : Nat} (U : Mat d)
    (hU : IsUnitary U) (A : a → Mat d) : familyHS (fun a => U*A a)=familyHS A := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  simp only [familyHS_sq,hsNorm_unitary_left U _ hU.1]

theorem familyHS_commutator_left {a : Type*} [Fintype a] {d : Nat}
    (C Q : Mat d) (hC : IsInvolution C) (hQ : IsInvolution Q) (A : a → Mat d) :
    familyHS (fun a => comm C Q*A a)≤2*familyHS A := by
  have he : (fun a => comm C Q*A a)=(fun a => (C*Q)*A a-(Q*C)*A a) := by
    funext a
    simp only [comm,Matrix.sub_mul]
  rw [he]
  have h := familyHS_sub_le (fun a => (C*Q)*A a) (fun a => (Q*C)*A a)
  rw [familyHS_left_unitary _ (unitary_mul _ _ (CountProof.involution_unitary C hC) (CountProof.involution_unitary Q hQ)) A,
    familyHS_left_unitary _ (unitary_mul _ _ (CountProof.involution_unitary Q hQ) (CountProof.involution_unitary C hC)) A] at h
  linarith

theorem commutator_branch_weight {a : Type*} [Fintype a] {d : Nat}
    (K : a → Mat d) (hK : ∑ a, K a*(K a).conjTranspose=1)
    (C Q eta : Mat d) (hC : IsInvolution C) (hQ : IsInvolution Q) :
    familyHS (fun a => comm C Q*K a*eta)≤hsNorm (comm C Q*eta)+
      2*familyHS (fun a => comm (K a) eta) := by
  have he : (fun a => comm C Q*K a*eta)=
      (fun a => (comm C Q*eta)*K a+comm C Q*comm (K a) eta) := by
    funext a
    simp only [comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := familyHS_add (fun a => (comm C Q*eta)*K a) (fun a => comm C Q*comm (K a) eta)
  rw [familyHS_right_parseval K hK (comm C Q*eta)] at h
  have hb := familyHS_commutator_left C Q hC hQ (fun a => comm (K a) eta)
  linarith

theorem projection_pair_commutator {d : Nat} (C Q : Mat d) (b : Bool) :
    comm C (signProjection Q b)=(if b then (-1/2:ℂ) else 1/2) • comm C Q := by
  cases b <;> simp only [signProjection,Bool.false_eq_true,↓reduceIte,comm,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,
    Matrix.neg_mul,Matrix.mul_neg]
  all_goals module

theorem familyHS_half_sign {a : Type*} [Fintype a] {d : Nat} (A : a → Mat d) :
    familyHS (fun t : Bool × a => (if t.1 then (-1/2:ℂ) else 1/2) • A t.2)=familyHS A/Real.sqrt 2 := by
  have ht (b : Bool) (a : a) : hsNorm ((if b then (-1/2:ℂ) else 1/2) • A a)=hsNorm (A a)/2 := by
    cases b <;> simp [hsNorm_eq_frobenius,norm_smul,div_eq_mul_inv,mul_comm]
  apply (sq_eq_sq₀ (familyHS_nonneg _) (div_nonneg (familyHS_nonneg _) (Real.sqrt_nonneg _))).mp
  simp only [familyHS_sq,Fintype.sum_prod_type,ht,Fintype.sum_bool]
  simp only [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),familyHS_sq,← Finset.sum_div]
  ring

theorem disturbance_step {a : Type*} [Fintype a] {d : Nat} (K : a → Mat d)
    (hK : ∑ a, K a*(K a).conjTranspose=1) (C Q eta : Mat d)
    (hC : IsInvolution C) (hQ : IsInvolution Q) :
    familyHS (fun t : Bool × a => comm C (signProjection Q t.1*K t.2)*eta)≤
      familyHS (fun a => comm C (K a)*eta)+
      (hsNorm (comm C Q*eta)+2*familyHS (fun a => comm (K a) eta))/Real.sqrt 2 := by
  have he : (fun t : Bool × a => comm C (signProjection Q t.1*K t.2)*eta)=
      (fun t => signProjection Q t.1*(comm C (K t.2)*eta)+
        (if t.1 then (-1/2:ℂ) else 1/2) • (comm C Q*K t.2*eta)) := by
    funext t
    rw [← Matrix.smul_mul,← Matrix.smul_mul,← projection_pair_commutator]
    simp only [comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := familyHS_add
    (fun t : Bool × a => signProjection Q t.1*(comm C (K t.2)*eta))
    (fun t : Bool × a => (if t.1 then (-1/2:ℂ) else 1/2) • (comm C Q*K t.2*eta))
  rw [familyHS_pair_left (signProjection Q) (CountProof.symmetryProjection_complete Q hQ)
    (fun a => comm C (K a)*eta),familyHS_half_sign (fun a => comm C Q*K a*eta)] at h
  have hb := div_le_div_of_nonneg_right (commutator_branch_weight K hK C Q eta hC hQ) (Real.sqrt_nonneg 2)
  linarith

end
end Companion.Analytic.ReturnProof
