import Companion.RecordParity

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open TransferProof
open Classical
set_option maxHeartbeats 600000

theorem kraus_projection_expectation {d : Nat} (psi K Q : Mat d)
    (hQ : Q.conjTranspose=Q) (hQQ : Q*Q=Q) :
    expectation psi (K.conjTranspose*K) Q=hsNorm (Q*psi*K.transpose)^2 := by
  let X := psi*K.transpose
  rw [Matrix.mul_assoc Q psi K.transpose]
  have he : (Q*X).conjTranspose*(Q*X)=X.conjTranspose*Q*X := by
    rw [Matrix.conjTranspose_mul,hQ]
    calc
      _=X.conjTranspose*(Q*Q)*X := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hQQ]
  change expectation psi (K.conjTranspose*K) Q=hsNorm (Q*X)^2
  rw [hsNorm_sq,hsSquared_trace,he,expectation_trace]
  have ht : (psi.conjTranspose*((Q*psi)*(K.conjTranspose*K).transpose)).trace=
      (X.conjTranspose*Q*X).trace := by
    calc
      _=((psi.conjTranspose*(Q*psi)*K.transpose)*(K.conjTranspose).transpose).trace := by
        simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=((K.conjTranspose).transpose*(psi.conjTranspose*(Q*psi)*K.transpose)).trace :=
        Matrix.trace_mul_comm _ _
      _=_ := by simp only [X,Matrix.conjTranspose_mul,
        Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,Matrix.mul_assoc]
  rw [ht]

theorem binary_branch_complete {d : Nat} (B A : Mat d) (hB : IsInvolution B) (b : Bool) :
    hsNorm (signProjection B b*A)^2+hsNorm (signProjection B (!b)*A)^2=hsNorm A^2 := by
  have h := CountProof.measurement_parseval (signProjection B)
    (CountProof.symmetryProjection_complete B hB) A
  cases b <;> simpa only [Fintype.sum_bool,Bool.not_false,Bool.not_true,add_comm] using h

theorem binary_branch_le {d : Nat} (B A : Mat d) (hB : IsInvolution B) (b : Bool) :
    hsNorm (signProjection B b*A)^2≤hsNorm A^2 := by
  have h := binary_branch_complete B A hB b
  nlinarith [sq_nonneg (hsNorm (signProjection B (!b)*A))]

theorem binary_mismatch_identity {d : Nat} (B A : Mat d) (b : Bool) :
    hsNorm (signProjection B (!b)*A)^2=hsNorm (B*A-boolPhase b • A)^2/4 := by
  have he : signProjection B (!b)*A=
      (if b then (1/2:ℂ) else -1/2) • (B*A-boolPhase b • A) := by
    cases b <;> simp only [signProjection,boolPhase,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      ↓reduceIte,Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,Matrix.neg_mul]
    all_goals module
  rw [he]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,hsNorm_eq_frobenius,norm_smul]
  all_goals norm_num; ring

theorem corrected_branch_bound {d : Nat} (g : LCS) (i : Fin g.system.equations.length)
    (B A : Mat d) (hB : IsInvolution B) (a : Fin g.system.n → Bool) (j : Fin g.system.n) :
    hsNorm (signProjection B (!(correctedAnswer g i a j))*A)^2≤
      hsNorm (signProjection B (!(a j))*A)^2+
        if ¬validAnswer g i a then hsNorm A^2 else 0 := by
  classical
  by_cases ha : validAnswer g i a
  · rw [correctedAnswer_fixed_valid g i a ha,ite_eq_right (not_not.mpr ha),add_zero]
  · rw [ite_eq_left ha]
    have h := binary_branch_le B A hB (!(correctedAnswer g i a j))
    nlinarith [sq_nonneg (hsNorm (signProjection B (!(a j))*A))]

end
end Companion.Analytic.ReturnProof
