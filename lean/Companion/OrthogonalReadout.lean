import Companion.JointOrthogonality

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 500000

variable {a z : Type*} [Fintype a] [DecidableEq a] [Fintype z] [DecidableEq z]

def readoutIsometry (P : z → Matrix a a ℂ) : Matrix (a × z) a ℂ :=
  fun aj b => P aj.2 aj.1 b

theorem readoutIsometry_isometry (P : z → Matrix a a ℂ)
    (hP : ∑ j, (P j).conjTranspose*P j=1) :
    (readoutIsometry P).conjTranspose*readoutIsometry P=1 := by
  rw [← hP]
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,readoutIsometry,
    Fintype.sum_prod_type,Matrix.sum_apply]
  exact Finset.sum_comm

theorem readoutIsometry_matrix (P : z → Matrix a a ℂ) (A : Matrix a a ℂ)
    (i j : a) (s t : z) :
    (readoutIsometry P*A*(readoutIsometry P).conjTranspose) (i,s) (j,t)=
      (P s*A*(P t).conjTranspose) i j := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,readoutIsometry]

theorem orthogonal_sandwich (P : z → Matrix a a ℂ)
    (hm : ∀ s t, P s*P t=if s=t then P s else 0) (A : Matrix a a ℂ) (s t : z) :
    P s*(∑ j, P j*A*P j)*P t=if s=t then P s*A*P s else 0 := by
  calc
    _=∑ j, (P s*P j)*A*(P j*P t) := by
      simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
    _=∑ j, if j=s then (if j=t then P j*A*P j else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hm s j,hm j t]
      by_cases hj : j=s
      · subst j
        simp only [↓reduceIte]
        split <;> simp_all
      · simp [hj,Ne.symm hj]
    _=_ := by simp

/-- The entropy of a genuine orthogonal pinching is at least the Shannon
entropy of its joint outcome weights. This is an isometry proof, not an
assumed entropy monotonicity for a measurement. -/
theorem orthogonal_pinching_entropy_lower (P : z → Matrix a a ℂ)
    (hh : ∀ j, (P j).conjTranspose=P j)
    (hm : ∀ s t, P s*P t=if s=t then P s else 0)
    (hP : ∑ j, (P j).conjTranspose*P j=1) (rho sigma : QIT.State a)
    (hsigma : sigma.matrix=∑ j, P j*rho.matrix*P j) :
    (∑ j, Real.negMulLog (P j*rho.matrix*P j).trace.re)/Real.log 2≤sigma.vonNeumann := by
  let tau := isometryState sigma (readoutIsometry P) (readoutIsometry_isometry P hP)
  have ht : tau.matrix=Matrix.blockDiagonal (fun j => P j*rho.matrix*P j) := by
    ext ⟨i,s⟩ ⟨j,t⟩
    change (readoutIsometry P*sigma.matrix*(readoutIsometry P).conjTranspose) (i,s) (j,t)=_
    rw [readoutIsometry_matrix,hh t,hsigma,orthogonal_sandwich P hm]
    by_cases he : s=t
    · subst t; simp [Matrix.blockDiagonal_apply]
    · simp [he,Ne.symm he,Matrix.blockDiagonal_apply]
  have hb (j : z) : (P j*rho.matrix*P j).PosSemidef := by
    simpa only [hh j] using rho.pos.mul_mul_conjTranspose_same (P j)
  have h := block_entropy_lower tau _ hb ht
  rw [isometryState_entropy] at h
  exact h

theorem orthogonal_factor_entropy_lower {b : Type*} [Fintype b]
    (P : z → Matrix a a ℂ) (hh : ∀ j, (P j).conjTranspose=P j)
    (hm : ∀ s t, P s*P t=if s=t then P s else 0)
    (hP : ∑ j, (P j).conjTranspose*P j=1) (K : Matrix a b ℂ) (hK : hsNorm K=1)
    (sigma : QIT.State a) (hsigma : sigma.matrix=∑ j, P j*(K*K.conjTranspose)*P j) :
    (∑ j, Real.negMulLog (hsNorm (P j*K)^2))/Real.log 2≤sigma.vonNeumann := by
  have he (j : z) : (P j*(K*K.conjTranspose)*P j).trace.re=hsNorm (P j*K)^2 := by
    have hm0 : P j*(K*K.conjTranspose)*P j=(P j*K)*(P j*K).conjTranspose := by
      simp only [Matrix.conjTranspose_mul,hh j,Matrix.mul_assoc]
    rw [hm0,Matrix.trace_mul_comm,gram_trace,Complex.ofReal_re,hsNorm_sq]
  have h := orthogonal_pinching_entropy_lower P hh hm hP (factorState K hK) sigma hsigma
  simp only [factorState,he] at h
  exact h

end
end Companion.Analytic.CountProof
