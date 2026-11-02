import Blueprint.RatesDefinitions
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators Kronecker
set_option maxHeartbeats 600000

def pauli : Fin 3 → Mat 2 := ![!![0,1;1,0],!![0,-Complex.I;Complex.I,0],!![1,0;0,-1]]

theorem pauli_involution (i : Fin 3) : IsInvolution (pauli i) := by
  fin_cases i <;> constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.conjTranspose_apply,Complex.ext_iff]

theorem pauli_anti (i j : Fin 3) (hij : i≠j) : pauli i*pauli j+pauli j*pauli i=0 := by
  fin_cases i <;> fin_cases j <;> simp_all <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,Matrix.mul_apply,Fin.sum_univ_succ,Complex.ext_iff]

theorem tensor_involution {a b : Nat} (P : Mat a) (Q : Mat b)
    (hP : IsInvolution P) (hQ : IsInvolution Q) :
    (P ⊗ₖ Q).conjTranspose=P ⊗ₖ Q ∧ (P ⊗ₖ Q)*(P ⊗ₖ Q)=1 := by
  constructor
  · rw [Matrix.conjTranspose_kronecker,hP.1,hQ.1]
  · rw [←Matrix.mul_kronecker_mul,hP.2,hQ.2,Matrix.one_kronecker_one]

theorem tensor_anti_left {d : Nat} (P Q : Mat 2) (R : Mat d)
    (hPQ : P*Q+Q*P=0) :
    (P ⊗ₖ (1:Mat d))*(Q ⊗ₖ R)+(Q ⊗ₖ R)*(P ⊗ₖ (1:Mat d))=0 := by
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.mul_one,←Matrix.add_kronecker,hPQ,Matrix.zero_kronecker]

theorem tensor_anti_right {d : Nat} (P : Mat 2) (R S : Mat d)
    (hP : P*P=1) (hRS : R*S+S*R=0) :
    (P ⊗ₖ R)*(P ⊗ₖ S)+(P ⊗ₖ S)*(P ⊗ₖ R)=0 := by
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,hP,
    ←Matrix.kronecker_add,hRS,Matrix.kronecker_zero]

def cliffordStep {k d : Nat} (A : Fin k → Mat d) :
    Fin (k+2) → Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  Fin.cases (pauli 0 ⊗ₖ (1:Mat d))
    (Fin.cases (pauli 1 ⊗ₖ (1:Mat d)) (fun j => pauli 2 ⊗ₖ A j))

theorem cliffordStep_involution {k d : Nat} (A : Fin k → Mat d)
    (hA : ∀ i, IsInvolution (A i)) (i : Fin (k+2)) :
    (cliffordStep A i).conjTranspose=cliffordStep A i ∧
      cliffordStep A i*cliffordStep A i=1 := by
  refine Fin.cases ?_ (Fin.cases ?_ ?_) i
  · exact tensor_involution _ _ (pauli_involution 0) (by simp [IsInvolution])
  · exact tensor_involution _ _ (pauli_involution 1) (by simp [IsInvolution])
  · intro j
    exact tensor_involution _ _ (pauli_involution 2) (hA j)

theorem cliffordStep_anti {k d : Nat} (A : Fin k → Mat d)
    (hA : ∀ i j, i≠j → A i*A j+A j*A i=0) (i j : Fin (k+2)) (hij : i≠j) :
    cliffordStep A i*cliffordStep A j+cliffordStep A j*cliffordStep A i=0 := by
  revert j
  refine Fin.cases ?_ (Fin.cases ?_ ?_) i
  · intro j
    refine Fin.cases ?_ (Fin.cases ?_ ?_) j
    · exact fun h => (h rfl).elim
    · intro _
      exact tensor_anti_left _ _ _ (pauli_anti 0 1 (by decide))
    · intro j _
      exact tensor_anti_left _ _ _ (pauli_anti 0 2 (by decide))
  · intro j
    refine Fin.cases ?_ (Fin.cases ?_ ?_) j
    · intro _
      simpa only [cliffordStep,Fin.cases_zero,Fin.cases_succ,add_comm] using tensor_anti_left (pauli 0) (pauli 1) (1:Mat d) (pauli_anti 0 1 (by decide))
    · exact fun h => (h rfl).elim
    · intro j _
      exact tensor_anti_left _ _ _ (pauli_anti 1 2 (by decide))
  · intro i j
    refine Fin.cases ?_ (Fin.cases ?_ ?_) j
    · intro _
      simpa only [cliffordStep,Fin.cases_zero,Fin.cases_succ,add_comm] using tensor_anti_left (pauli 0) (pauli 2) (A i) (pauli_anti 0 2 (by decide))
    · intro _
      simpa only [cliffordStep,Fin.cases_zero,Fin.cases_succ,add_comm] using tensor_anti_left (pauli 1) (pauli 2) (A i) (pauli_anti 1 2 (by decide))
    · intro j h
      exact tensor_anti_right _ _ _ (pauli_involution 2).2 (hA i j (fun he => h (by rw [he])))

theorem reindex_involution {α : Type*} [Fintype α] [DecidableEq α] {d : Nat}
    (e : α ≃ Fin d) (P : Matrix α α ℂ) (hP : P.conjTranspose=P ∧ P*P=1) :
    IsInvolution (Matrix.reindex e e P) := by
  constructor
  · rw [Matrix.conjTranspose_reindex,hP.1]
  · change Matrix.reindexAlgEquiv ℂ ℂ e P*Matrix.reindexAlgEquiv ℂ ℂ e P=1
    rw [←map_mul,hP.2,map_one]

theorem clifford_family (m : Nat) : ∃ A : Fin (2*m+1) → Mat (2^m),
    (∀ i, IsInvolution (A i)) ∧ ∀ i j, i≠j → A i*A j+A j*A i=0 := by
  induction m with
  | zero =>
    refine ⟨fun _ => 1,fun _ => by simp [IsInvolution],?_⟩
    intro i j hij
    exact (hij (Fin.ext (by omega))).elim
  | succ m ih =>
    obtain ⟨A,hA,hanti⟩ := ih
    let e : Fin 2 × Fin (2^m) ≃ Fin (2^(m+1)) :=
      finProdFinEquiv.trans (finCongr (by rw [pow_succ]; omega))
    let f : Fin (2*(m+1)+1) → Fin ((2*m+1)+2) :=
      Fin.cast (by omega)
    refine ⟨fun i => Matrix.reindex e e (cliffordStep A (f i)),?_,?_⟩
    · intro i
      exact reindex_involution e _ (cliffordStep_involution A hA (f i))
    · intro i j hij
      have h := cliffordStep_anti A hanti (f i) (f j) (fun he => hij (Fin.ext (congrArg Fin.val he)))
      have h' := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) h
      simpa only [map_add,map_mul,map_zero,Matrix.coe_reindexAlgEquiv] using h'

end
end Blueprint.W2
