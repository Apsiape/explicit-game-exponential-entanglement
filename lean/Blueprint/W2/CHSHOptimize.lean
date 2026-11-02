import Blueprint.RatesDefinitions
import Companion.HermitianOptimization

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

theorem contraction_complements {d : Nat} (A : Mat d) (hA : contraction A) :
    (1+A).PosSemidef ∧ (1-A).PosSemidef := by
  by_cases hd : d=0
  · subst d
    have h0 : (1:Mat 0)=0 := Subsingleton.elim _ _
    have hA0 : A=0 := Subsingleton.elim _ _
    simp [h0,hA0,Matrix.PosSemidef.zero]
  letI : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  have upper (T : Mat d) (hT : T.IsHermitian) (hn : ‖T‖≤1) : T≤1 := by
    have hs : IsSelfAdjoint T := hT
    have h : T≤algebraMap ℝ (Mat d) 1 := le_algebraMap_of_spectrum_le (a:=T) (ha:=hs) (by
      intro r hr
      exact (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans hn))
    simpa only [map_one] using h
  have hp := upper (-A) hA.1.neg (by simpa using hA.2)
  have hm := upper A hA.1 hA.2
  exact ⟨by simpa only [sub_neg_eq_add] using Matrix.le_iff.mp hp,Matrix.le_iff.mp hm⟩

def payoffSign {d : Nat} (H : Mat d) (hH : H.IsHermitian) : Mat d :=
  TransferProof.projectionInvolution (TransferProof.positiveSpectralProjector H hH)

theorem payoffSign_involution {d : Nat} (H : Mat d) (hH : H.IsHermitian) :
    IsInvolution (payoffSign H hH) :=
  TransferProof.projectionInvolution_involution _
    (TransferProof.positiveSpectralProjector_hermitian _ _)
    (TransferProof.positiveSpectralProjector_square _ _)

theorem payoffSign_optimal {d : Nat} (H A : Mat d) (hH : H.IsHermitian) (hA : contraction A) :
    (A*H).trace.re≤(payoffSign H hH*H).trace.re := by
  let E := (1/2:ℂ) • (1+A)
  have hp := contraction_complements A hA
  have hE : E.PosSemidef := hp.1.smul (by constructor <;> norm_num)
  have hEc : (1-E).PosSemidef := by
    have he : 1-E=(1/2:ℂ) • (1-A) := by dsimp [E]; module
    rw [he]
    exact hp.2.smul (by constructor <;> norm_num)
  have h := TransferProof.positiveSpectralProjector_optimal H E hH hE hEc
  simp only [E,payoffSign,TransferProof.projectionInvolution,Matrix.smul_mul,Matrix.add_mul,
    Matrix.sub_mul,Matrix.one_mul,Matrix.trace_smul,Matrix.trace_add,Matrix.trace_sub,
    Complex.add_re,Complex.sub_re,Complex.mul_re] at h ⊢
  norm_num at h ⊢
  linarith

theorem expectation_alice_trace {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (A : Mat a) (B : Mat b) :
    expectation psi A B=(A*((psi.conjTranspose*B*psi).transpose)).trace.re := by
  rw [TransferProof.expectation_trace]
  have he : (psi.conjTranspose*(B*psi)*A.transpose).trace=
      (A*(psi.conjTranspose*B*psi).transpose).trace := by
    rw [←Matrix.trace_transpose,Matrix.transpose_mul,Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc] using congrArg Complex.re he

theorem hermitian_finite_sum {ι : Type*} [Fintype ι] {d : Nat} (F : ι → Mat d)
    (hF : ∀ i, (F i).IsHermitian) : (∑ i, F i).IsHermitian := by
  change (∑ i, F i).conjTranspose=∑ i, F i
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => (hF i).eq)

def alicePayoff {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (B : Fin n → Fin n → Mat b) (i : Fin n) : Mat a :=
  ∑ p, ∑ q, if p<q then
    (if i=p then (psi.conjTranspose*(B p q+B q p)*psi).transpose else 0)+
    (if i=q then (psi.conjTranspose*(B p q-B q p)*psi).transpose else 0) else 0

theorem alicePayoff_hermitian {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (B : Fin n → Fin n → Mat b) (hB : ∀ i j, i≠j → (B i j).IsHermitian) (i : Fin n) :
    (alicePayoff psi B i).IsHermitian := by
  apply hermitian_finite_sum
  intro p
  apply hermitian_finite_sum
  intro q
  split
  · have hpq := hB p q (ne_of_lt ‹_›)
    have hqp := hB q p (ne_of_gt ‹_›)
    apply Matrix.IsHermitian.add
    · split
      · exact (Matrix.isHermitian_conjTranspose_mul_mul psi (hpq.add hqp)).transpose
      · exact Matrix.isHermitian_zero
    · split
      · exact (Matrix.isHermitian_conjTranspose_mul_mul psi (hpq.sub hqp)).transpose
      · exact Matrix.isHermitian_zero
  · exact Matrix.isHermitian_zero

theorem alicePayoff_total {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) :
    (∑ i, (A i*alicePayoff psi B i).trace.re)=
      ∑ p, ∑ q, if p<q then chshPair psi A B p q else 0 := by
  simp only [alicePayoff,Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpq : p<q
  · simp only [hpq,↓reduceIte,Matrix.mul_add,Matrix.trace_add,Complex.add_re,Finset.sum_add_distrib]
    have point (H : Mat a) (r : Fin n) :
        (∑ i, (A i*(if i=r then H else 0)).trace.re)=(A r*H).trace.re := by
      calc
        _=∑ i, if i=r then (A r*H).trace.re else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i=r <;> simp [hi]
        _=_ := by simp
    rw [point,point]
    simpa only [chshPair,Matrix.mul_add] using
      (congrArg₂ (·+·) (expectation_alice_trace psi (A p) (B p q+B q p))
        (expectation_alice_trace psi (A q) (B p q-B q p))).symm
  · simp [hpq]

def bobPlusPayoff {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (i j : Fin n) : Mat b :=
  psi*(A i+A j).transpose*psi.conjTranspose

def bobMinusPayoff {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (i j : Fin n) : Mat b :=
  psi*(A i-A j).transpose*psi.conjTranspose

theorem bobPlusPayoff_hermitian {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (hA : ∀ i, (A i).IsHermitian) (i j : Fin n) :
    (bobPlusPayoff psi A i j).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose psi ((hA i).add (hA j)).transpose

theorem bobMinusPayoff_hermitian {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (hA : ∀ i, (A i).IsHermitian) (i j : Fin n) :
    (bobMinusPayoff psi A i j).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose psi ((hA i).sub (hA j)).transpose

theorem bobPayoff_pair {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) (i j : Fin n) :
    chshPair psi A B i j=(B i j*bobPlusPayoff psi A i j).trace.re+
      (B j i*bobMinusPayoff psi A i j).trace.re := by
  simp only [chshPair,TransferProof.expectation_bob_trace,bobPlusPayoff,bobMinusPayoff,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,
    Matrix.sub_mul,Matrix.trace_add,Matrix.trace_sub,Complex.add_re,Complex.sub_re]
  ring

def optimizedBob {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (hA : ∀ i, (A i).IsHermitian) (i j : Fin n) : Mat b :=
  if i < j then payoffSign (bobPlusPayoff psi A i j) (bobPlusPayoff_hermitian psi A hA i j)
  else if j < i then payoffSign (bobMinusPayoff psi A j i) (bobMinusPayoff_hermitian psi A hA j i)
  else 1

theorem optimizedBob_involution {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (hA : ∀ i, (A i).IsHermitian) (i j : Fin n) :
    IsInvolution (optimizedBob psi A hA i j) := by
  unfold optimizedBob
  split
  · exact payoffSign_involution _ _
  · split
    · exact payoffSign_involution _ _
    · simp [IsInvolution]

theorem optimizedBob_pair {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b)
    (hA : ∀ i, (A i).IsHermitian) (hB : ∀ i j, i≠j → contraction (B i j))
    (i j : Fin n) (hij : i<j) :
    chshPair psi A B i j≤chshPair psi A (optimizedBob psi A hA) i j := by
  rw [bobPayoff_pair,bobPayoff_pair]
  simp only [optimizedBob,hij,not_lt_of_ge hij.le,↓reduceIte]
  exact add_le_add
    (payoffSign_optimal _ _ (bobPlusPayoff_hermitian psi A hA i j) (hB i j (ne_of_lt hij)))
    (payoffSign_optimal _ _ (bobMinusPayoff_hermitian psi A hA i j) (hB j i (ne_of_gt hij)))

end
end Blueprint.W2
