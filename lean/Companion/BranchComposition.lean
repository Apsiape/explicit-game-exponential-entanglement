import Companion.SequentialNormalization

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 600000

theorem familyHS_pair_left {a b : Type*} [Fintype a] [Fintype b] {d : Nat}
    (P : a → Mat d) (hP : ∑ t, (P t).conjTranspose*P t=1) (A : b → Mat d) :
    familyHS (fun t : a × b => P t.1*A t.2)=familyHS A := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  rw [familyHS_sq,familyHS_sq,Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [CountProof.measurement_parseval P hP]

theorem familyHS_pair_right {a b : Type*} [Fintype a] [Fintype b] {d : Nat}
    (P : a → Mat d) (hP : ∑ t, P t*(P t).conjTranspose=1) (A : b → Mat d) :
    familyHS (fun t : b × a => A t.1*P t.2)=familyHS A := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  rw [familyHS_sq,familyHS_sq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  change (∑ y, hsNorm (A t*P y)^2)=hsNorm (A t)^2
  rw [← familyHS_sq,familyHS_right_parseval P hP (A t)]

theorem composition_commutator_bound {a b : Type*} [Fintype a] [Fintype b] {d : Nat}
    (P : a → Mat d) (K : b → Mat d) (eta : Mat d)
    (hP : ∑ t, (P t).conjTranspose*P t=1) (hK : ∑ t, K t*(K t).conjTranspose=1) :
    familyHS (fun t : a × b => comm (P t.1*K t.2) eta)≤
      familyHS (fun t => comm (K t) eta)+familyHS (fun t => comm (P t) eta) := by
  have he : (fun t : a × b => comm (P t.1*K t.2) eta)=
      (fun t => P t.1*comm (K t.2) eta+comm (P t.1) eta*K t.2) := by
    funext t
    simp only [comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := familyHS_add (fun t : a × b => P t.1*comm (K t.2) eta)
    (fun t : a × b => comm (P t.1) eta*K t.2)
  rw [familyHS_pair_left P hP (fun t => comm (K t) eta),
    familyHS_pair_right K hK (fun t => comm (P t) eta)] at h
  exact h

theorem familyHS_cube_cons {d n : Nat} (F : (Fin (n+1) → Bool) → Mat d) :
    familyHS F=familyHS (fun t : Bool × (Fin n → Bool) => F (Fin.cons t.1 t.2)) := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  rw [familyHS_sq,familyHS_sq,sum_cube_succ,Fintype.sum_prod_type]

theorem familyHS_swap {a b : Type*} [Fintype a] [Fintype b] {d : Nat}
    (F : a → b → Mat d) :
    familyHS (fun t : a × b => F t.1 t.2)=familyHS (fun t : b × a => F t.2 t.1) := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  simp only [familyHS_sq,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem projection_commutator {d : Nat} (Q eta : Mat d) (b : Bool) :
    comm (signProjection Q b) eta=(if b then (-1/2:ℂ) else 1/2) • comm Q eta := by
  cases b <;> simp only [signProjection,Bool.false_eq_true,↓reduceIte,comm,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,
    Matrix.neg_mul,Matrix.mul_neg]
  all_goals module

theorem projection_commutator_norm {d : Nat} (Q eta : Mat d) :
    familyHS (fun b : Bool => comm (signProjection Q b) eta)=hsNorm (comm Q eta)/Real.sqrt 2 := by
  have ht (b : Bool) : hsNorm (comm (signProjection Q b) eta)=hsNorm (comm Q eta)/2 := by
    rw [projection_commutator]
    cases b <;> simp [hsNorm_eq_frobenius,norm_smul,div_eq_mul_inv,mul_comm]
  apply (sq_eq_sq₀ (familyHS_nonneg _) (div_nonneg (hsNorm_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [familyHS_sq]
  simp only [ht,Fintype.sum_bool]
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  simp only [div_pow,h2]
  ring

end
end Companion.Analytic.ReturnProof
