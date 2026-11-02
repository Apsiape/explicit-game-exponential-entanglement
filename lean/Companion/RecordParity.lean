import Companion.RecordProducts
import Companion.BranchDisturbance

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open TransferProof
set_option maxHeartbeats 600000

theorem hsNorm_transpose {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b ℂ) :
    hsNorm X.transpose=hsNorm X := by
  apply congrArg Real.sqrt
  exact Finset.sum_comm

theorem transposedKraus_coComplete {a : Type*} [Fintype a] {d : Nat} (K : a → Mat d)
    (hK : ∑ a, (K a).conjTranspose*K a=1) :
    (∑ a, (K a).transpose*((K a).transpose).conjTranspose)=1 := by
  have h := congrArg Matrix.transpose hK
  simpa only [Matrix.transpose_sum,Matrix.transpose_mul,Matrix.transpose_one,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose] using h

def recordParity {n : Nat} (a : Fin n → Bool) : Bool := (List.ofFn a).foldl Bool.xor false

theorem phaseProduct_parity {n : Nat} (a : Fin n → Bool) :
    phaseProduct n (fun j a => a j) a=boolPhase (recordParity a) := by
  unfold phaseProduct recordParity
  simpa only [List.map_ofFn,Function.comp_def] using boolPhase_parity (List.ofFn a)

def parityMass {d n : Nat} (K : (Fin n → Bool) → Mat d) (xi : Mat d) (rhs : Bool) : ℝ :=
  ∑ a, if recordParity a≠rhs then hsNorm (xi*(K a).transpose)^2 else 0

theorem parityMass_nonneg {d n : Nat} (K : (Fin n → Bool) → Mat d) (xi : Mat d) (rhs : Bool) :
    0≤parityMass K xi rhs := by
  apply Finset.sum_nonneg
  intro a _
  split <;> positivity

theorem parityMass_identity {d n : Nat} (K : (Fin n → Bool) → Mat d) (xi : Mat d) (rhs : Bool) :
    familyHS (fun a => (boolPhase (recordParity a)-boolPhase rhs) • (xi*(K a).transpose))^2=
      4*parityMass K xi rhs := by
  rw [familyHS_sq,parityMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  cases recordParity a <;> cases rhs <;>
    norm_num [boolPhase,hsNorm_eq_frobenius,norm_smul] <;> ring

theorem record_parity_bound {d n : Nat} (B : Fin n → Mat d) (hB : ∀ j, IsInvolution (B j))
    (K : (Fin n → Bool) → Mat d) (hK : ∑ a, (K a).conjTranspose*K a=1) (xi : Mat d) (rhs : Bool) :
    parityMass K xi rhs≤(hsNorm (((List.ofFn B).prod-boolPhase rhs • (1:Mat d))*xi)+
      ∑ j, familyHS (fun a => B j*(xi*(K a).transpose)-boolPhase (a j) • (xi*(K a).transpose)))^2/4 := by
  let A := fun a => xi*(K a).transpose
  let P := (List.ofFn B).prod
  have he : (fun a => (boolPhase (recordParity a)-boolPhase rhs) • A a)=
      (fun a => ((P-boolPhase rhs • (1:Mat d))*xi)*(K a).transpose-
        (P*A a-phaseProduct n (fun j a => a j) a • A a)) := by
    funext a
    rw [phaseProduct_parity]
    dsimp only [A]
    simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc,sub_smul]
    abel
  have h := familyHS_sub_le
    (fun a => ((P-boolPhase rhs • (1:Mat d))*xi)*(K a).transpose)
    (fun a => P*A a-phaseProduct n (fun j a => a j) a • A a)
  rw [← he,familyHS_right_parseval (fun a => (K a).transpose) (transposedKraus_coComplete K hK)] at h
  have hp := record_product_mismatch n B hB (fun j a => a j) A
  have hb : familyHS (fun a => (boolPhase (recordParity a)-boolPhase rhs) • A a)≤
      hsNorm ((P-boolPhase rhs • (1:Mat d))*xi)+
        ∑ j, familyHS (fun a => B j*A a-boolPhase (a j) • A a) := by linarith
  have hn := familyHS_nonneg (fun a => (boolPhase (recordParity a)-boolPhase rhs) • A a)
  have hi := parityMass_identity K xi rhs
  change familyHS (fun a => (boolPhase (recordParity a)-boolPhase rhs) • A a)^2=4*parityMass K xi rhs at hi
  change parityMass K xi rhs≤(hsNorm ((P-boolPhase rhs • (1:Mat d))*xi)+
    ∑ j, familyHS (fun a => B j*A a-boolPhase (a j) • A a))^2/4
  nlinarith [sq_nonneg (hsNorm ((P-boolPhase rhs • (1:Mat d))*xi)+
    ∑ j, familyHS (fun a => B j*A a-boolPhase (a j) • A a))]

theorem sequential_record_parity_bound {d n : Nat} (B : Fin n → Mat d)
    (hB : ∀ j, IsInvolution (B j)) (xi : Mat d) (rhs : Bool) :
    parityMass (CountProof.jointProjection n (fun j => (B j).transpose)) xi rhs≤
      (hsNorm (((List.ofFn B).prod-boolPhase rhs • (1:Mat d))*xi)+
        ∑ j, familyHS (fun a => B j*(xi*(CountProof.jointProjection n (fun j => (B j).transpose) a).transpose)-
          boolPhase (a j) • (xi*(CountProof.jointProjection n (fun j => (B j).transpose) a).transpose)))^2/4 :=
  record_parity_bound B hB _ (CountProof.jointProjection_complete n _
    (fun j => transpose_involution _ (hB j))) xi rhs

end
end Companion.Analytic.ReturnProof
