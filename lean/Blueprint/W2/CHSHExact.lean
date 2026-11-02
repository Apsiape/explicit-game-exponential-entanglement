import Blueprint.W2.CHSHBookkeeping
import Blueprint.W2.CliffordMatrices

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

theorem involution_contraction {d : Nat} (hd : 0<d) (A : Mat d) (hA : IsInvolution A) :
    contraction A := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  refine ⟨hA.1,?_⟩
  exact le_of_eq (CStarRing.norm_coe_unitary (asUnitary A (CountProof.involution_unitary A hA)))

def chshPlus {d : Nat} (A B : Mat d) : Mat d := (((1/Real.sqrt 2:ℝ):ℂ)) • (A+B)

theorem chshPlus_involution {d : Nat} (A B : Mat d)
    (hA : IsInvolution A) (hB : IsInvolution B) (ha : anti A B=0) :
    IsInvolution (chshPlus A B) := by
  have hs : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have hcoef : (((1/Real.sqrt 2:ℝ):ℂ))*(((1/Real.sqrt 2:ℝ):ℂ))*(2:ℂ)=1 := by
    have hh : (1/Real.sqrt 2:ℝ)*(1/Real.sqrt 2)*2=1 := by
      field_simp
      nlinarith
    exact_mod_cast hh
  constructor
  · simp [chshPlus,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,hA.1,hB.1]
  · have hp : (A+B)*(A+B)=(2:ℂ) • (1:Mat d) := by
      calc
        _=A*A+anti A B+B*B := by noncomm_ring [anti]
        _=_ := by rw [hA.2,hB.2,ha]; module
    simp only [chshPlus,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hp]
    rw [←mul_assoc,hcoef,one_smul]

theorem neg_involution {d : Nat} (A : Mat d) (hA : IsInvolution A) : IsInvolution (-A) := by
  simpa [IsInvolution] using hA

theorem chshMinus_involution {d : Nat} (A B : Mat d)
    (hA : IsInvolution A) (hB : IsInvolution B) (ha : anti A B=0) :
    IsInvolution (chshPlus A (-B)) := by
  apply chshPlus_involution A (-B) hA (neg_involution B hB)
  have hh : anti A (-B)= -(anti A B) := by noncomm_ring [anti]
  rw [hh,ha,neg_zero]

def exactBob {n d : Nat} (A : Fin n → Mat d) (i j : Fin n) : Mat d :=
  if i < j then (chshPlus (A i) (A j)).transpose
  else if j < i then (chshPlus (A j) (-A i)).transpose else 1

theorem exactBob_involution {n d : Nat} (A : Fin n → Mat d)
    (hA : ∀ i, IsInvolution (A i)) (ha : ∀ i j, i≠j → anti (A i) (A j)=0)
    (i j : Fin n) : IsInvolution (exactBob A i j) := by
  unfold exactBob
  split
  · exact ReturnProof.transpose_involution _ (chshPlus_involution _ _ (hA i) (hA j) (ha i j (ne_of_lt ‹_›)))
  · split
    · exact ReturnProof.transpose_involution _ (chshMinus_involution _ _ (hA j) (hA i) (ha j i (ne_of_lt ‹_›)))
    · simp [IsInvolution]

theorem exactBob_pair {n d : Nat} (A : Fin n → Mat d) (i j : Fin n) (hij : i<j) :
    exactBob A i j+exactBob A j i=(((Real.sqrt 2:ℝ):ℂ)) • (A i).transpose ∧
      exactBob A i j-exactBob A j i=(((Real.sqrt 2:ℝ):ℂ)) • (A j).transpose := by
  have hh : (2:ℂ)*(((1/Real.sqrt 2:ℝ):ℂ))=((Real.sqrt 2:ℝ):ℂ) := by
    have hr : (2:ℝ)*(1/Real.sqrt 2)=Real.sqrt 2 := by
      have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
      field_simp
      nlinarith
    exact_mod_cast hr
  simp only [exactBob,hij,not_lt_of_ge hij.le,↓reduceIte,chshPlus,Matrix.transpose_smul,
    Matrix.transpose_add,Matrix.transpose_neg]
  constructor <;> rw [←hh] <;> module

theorem flat_expectation_real {d : Nat} (hd : 0<d) (A : Mat d) (hA : IsInvolution A) (r : ℝ) :
    expectation (MainProof.flatState d hd).xi A
      ((r:ℂ) • A.transpose)=r := by
  let s := MainProof.flatState d hd
  have hT : A.transpose*A.transpose=1 := by rw [←Matrix.transpose_mul,hA.2,Matrix.transpose_one]
  have hc : s.xi*A.transpose=A.transpose*s.xi := by
    rw [MainProof.flatState_xi]
    simp [Matrix.smul_mul,Matrix.mul_smul]
  have he : s.xi.conjTranspose*
      (((r:ℂ) • A.transpose)*s.xi*A.transpose)=
      (r:ℂ) • s.rho := by
    rw [s.xi_positive.isHermitian.eq,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul]
    congr 1
    calc
      _=s.xi*(A.transpose*(s.xi*A.transpose)) := by noncomm_ring
      _=s.xi*(A.transpose*(A.transpose*s.xi)) := by rw [hc]
      _=s.xi*((A.transpose*A.transpose)*s.xi) := by noncomm_ring
      _=s.xi*s.xi := by rw [hT,Matrix.one_mul]
      _=s.rho := s.xi_square
  rw [TransferProof.expectation_trace,he,Matrix.trace_smul,s.normalized]
  simp

theorem flat_expectation {d : Nat} (hd : 0<d) (A : Mat d) (hA : IsInvolution A) :
    expectation (MainProof.flatState d hd).xi A
      (((Real.sqrt 2:ℝ):ℂ) • A.transpose)=Real.sqrt 2 :=
  flat_expectation_real hd A hA (Real.sqrt 2)

theorem flat_entropy {d : Nat} (hd : 0<d) :
    entropy ((MainProof.flatState d hd).xi.conjTranspose*(MainProof.flatState d hd).xi)≤
      Real.log d/Real.log 2 := by
  rw [(MainProof.flatState d hd).xi_positive.isHermitian.eq,(MainProof.flatState d hd).xi_square]
  exact entropy_le_log_dimension _

end
end Blueprint.W2
