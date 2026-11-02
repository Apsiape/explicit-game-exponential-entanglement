import Companion.SequentialBranchBounds

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open TransferProof
set_option maxHeartbeats 600000

theorem familyHS_unit_scalar {a : Type*} [Fintype a] {d : Nat} (c : a → ℂ)
    (hc : ∀ a, ‖c a‖=1) (A : a → Mat d) :
    familyHS (fun a => c a • A a)=familyHS A := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  simp only [familyHS_sq]
  apply Finset.sum_congr rfl
  intro a _
  simp only [hsNorm_eq_frobenius,norm_smul,hc a,one_mul]

theorem familyHS_unitary_left {a : Type*} [Fintype a] {d : Nat} (U : Mat d)
    (hU : IsUnitary U) (A : a → Mat d) : familyHS (fun a => U*A a)=familyHS A := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  simp only [familyHS_sq,hsNorm_unitary_left U _ hU.1]

def phaseProduct {a : Type*} (n : Nat) (bits : Fin n → a → Bool) (a : a) : ℂ :=
  (List.ofFn (fun j => boolPhase (bits j a))).prod

theorem phaseProduct_norm {a : Type*} (n : Nat) (bits : Fin n → a → Bool) (a : a) :
    ‖phaseProduct n bits a‖=1 := by
  induction n with
  | zero => simp [phaseProduct]
  | succ n ih =>
    simp only [phaseProduct,List.ofFn_succ,List.prod_cons,norm_mul]
    change ‖boolPhase (bits 0 a)‖*‖phaseProduct n (Fin.tail bits) a‖=1
    rw [ih]
    cases bits 0 a <;> simp [boolPhase]

theorem record_product_mismatch {a : Type*} [Fintype a] {d : Nat} (n : Nat)
    (B : Fin n → Mat d) (hB : ∀ j, IsInvolution (B j))
    (bits : Fin n → a → Bool) (A : a → Mat d) :
    familyHS (fun a => (List.ofFn B).prod*A a-phaseProduct n bits a • A a)≤
      ∑ j, familyHS (fun a => B j*A a-boolPhase (bits j a) • A a) := by
  induction n with
  | zero => simp [phaseProduct,familyHS,stackMatrices,hsNorm,hsSquared]
  | succ n ih =>
    have he : (fun a => (List.ofFn B).prod*A a-phaseProduct (n+1) bits a • A a)=
        (fun a => B 0*((List.ofFn (Fin.tail B)).prod*A a-phaseProduct n (Fin.tail bits) a • A a)+
          phaseProduct n (Fin.tail bits) a • (B 0*A a-boolPhase (bits 0 a) • A a)) := by
      funext a
      have hp : phaseProduct (n+1) bits a=boolPhase (bits 0 a)*phaseProduct n (Fin.tail bits) a := by
        simp only [phaseProduct,List.ofFn_succ,List.prod_cons]
        rfl
      rw [hp,List.ofFn_succ,List.prod_cons]
      simp only [Matrix.mul_sub,Matrix.mul_smul,
        Matrix.mul_assoc,smul_sub,smul_smul]
      change B 0*((List.ofFn (Fin.tail B)).prod*A a)-
        (boolPhase (bits 0 a)*phaseProduct n (Fin.tail bits) a) • A a=_
      module
    rw [he]
    have h := familyHS_add
      (fun a => B 0*((List.ofFn (Fin.tail B)).prod*A a-phaseProduct n (Fin.tail bits) a • A a))
      (fun a => phaseProduct n (Fin.tail bits) a • (B 0*A a-boolPhase (bits 0 a) • A a))
    rw [familyHS_unitary_left _ (CountProof.involution_unitary _ (hB 0)),
      familyHS_unit_scalar _ (phaseProduct_norm n (Fin.tail bits))] at h
    have hi := ih (Fin.tail B) (fun j => hB j.succ) (Fin.tail bits)
    rw [Fin.sum_univ_succ]
    dsimp only [Fin.tail] at h hi ⊢
    linarith

end
end Companion.Analytic.ReturnProof
