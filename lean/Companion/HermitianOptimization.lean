import Companion.TransferRelationConstants

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

variable {d : Nat}

def positiveSpectralProjector (H : Mat d) (hH : H.IsHermitian) : Mat d :=
  let U := hH.eigenvectorUnitary
  (U:Mat d)*Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else 0)*(U:Mat d).conjTranspose

theorem positiveSpectralProjector_hermitian (H : Mat d) (hH : H.IsHermitian) :
    (positiveSpectralProjector H hH).IsHermitian := by
  let D := Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else 0)
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    split <;> simp
  change ((hH.eigenvectorUnitary:Mat d)*D*(hH.eigenvectorUnitary:Mat d).conjTranspose).conjTranspose=
    (hH.eigenvectorUnitary:Mat d)*D*(hH.eigenvectorUnitary:Mat d).conjTranspose
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hD.eq,Matrix.mul_assoc]

theorem positiveSpectralProjector_square (H : Mat d) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH*positiveSpectralProjector H hH=positiveSpectralProjector H hH := by
  let U := hH.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else 0)
  have hU : (U:Mat d).conjTranspose*(U:Mat d)=1 := U.property.1
  have hD : D*D=D := by
    change Matrix.diagonal _*Matrix.diagonal _=D
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split <;> simp
  change ((U:Mat d)*D*(U:Mat d).conjTranspose)*((U:Mat d)*D*(U:Mat d).conjTranspose)=_
  calc
    _=(U:Mat d)*(D*((U:Mat d).conjTranspose*(U:Mat d))*D)*(U:Mat d).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [hU,Matrix.mul_one,hD]; rfl

theorem trace_eigenbasis (H E : Mat d) (hH : H.IsHermitian) :
    (E*H).trace=(((hH.eigenvectorUnitary:Mat d).conjTranspose*E*(hH.eigenvectorUnitary:Mat d))*
      Matrix.diagonal (fun i => (hH.eigenvalues i:ℂ))).trace := by
  let U := hH.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i:ℂ))
  have hs : H=(U:Mat d)*D*(U:Mat d).conjTranspose := by
    exact hH.spectral_theorem
  change (E*H).trace=(((U:Mat d).conjTranspose*E*(U:Mat d))*D).trace
  rw [hs]
  calc
    _=(((E*(U:Mat d))*D)*(U:Mat d).conjTranspose).trace := by simp only [Matrix.mul_assoc]
    _=_ := by rw [Matrix.trace_mul_cycle]; simp only [Matrix.mul_assoc]

/-- Among all binary effects E, the positive spectral projector maximizes
the Hermitian payoff. No invertibility assumption on H or E is needed. -/
theorem positiveSpectralProjector_optimal (H E : Mat d) (hH : H.IsHermitian)
    (hE : E.PosSemidef) (hEc : (1-E).PosSemidef) :
    (E*H).trace.re≤(positiveSpectralProjector H hH*H).trace.re := by
  let U := hH.eigenvectorUnitary
  let A := (U:Mat d).conjTranspose*E*(U:Mat d)
  have hU : (U:Mat d).conjTranspose*(U:Mat d)=1 := U.property.1
  have hA : A.PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hE.mul_mul_conjTranspose_same (U:Mat d).conjTranspose
  have hAc : (1-A).PosSemidef := by
    have h := hEc.mul_mul_conjTranspose_same (U:Mat d).conjTranspose
    simpa only [Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hU,A] using h
  have hdiag (i : Fin d) : 0≤(A i i).re ∧ (A i i).re≤1 := by
    have h0 : (0:ℂ)≤A i i := hA.diag_nonneg
    have h1 : (0:ℂ)≤(1-A) i i := hAc.diag_nonneg
    constructor
    · exact h0.1
    · have h := h1.1
      simp only [Matrix.sub_apply,Matrix.one_apply_eq,Complex.sub_re,Complex.one_re,Complex.zero_re] at h
      linarith
  have hp : (U:Mat d).conjTranspose*positiveSpectralProjector H hH*(U:Mat d)=
      Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else 0) := by
    change (U:Mat d).conjTranspose*((U:Mat d)*_*(U:Mat d).conjTranspose)*(U:Mat d)=_
    calc
      _=((U:Mat d).conjTranspose*(U:Mat d))*
          Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else 0)*
            ((U:Mat d).conjTranspose*(U:Mat d)) := by
        simp only [Matrix.mul_assoc]
      _=_ := by rw [hU,Matrix.one_mul,Matrix.mul_one]
  rw [trace_eigenbasis H E hH,trace_eigenbasis H (positiveSpectralProjector H hH) hH,hp]
  change (A*Matrix.diagonal (fun i => (hH.eigenvalues i:ℂ))).trace.re≤_
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,Matrix.diagonal_apply_eq,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 0≤hH.eigenvalues i
  · simp only [hi,↓reduceIte,Complex.one_re,Complex.one_im,one_mul,zero_mul,sub_zero]
    exact mul_le_of_le_one_left hi (hdiag i).2
  · simp only [hi,↓reduceIte,Complex.zero_re,Complex.zero_im,zero_mul,sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hdiag i).1 (le_of_not_ge hi)

def projectionInvolution (P : Mat d) : Mat d := (2:ℂ) • P-1

theorem projectionInvolution_involution (P : Mat d) (hh : P.IsHermitian) (hp : P*P=P) :
    IsInvolution (projectionInvolution P) := by
  constructor
  · simp [projectionInvolution,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,hh.eq]
  · simp only [projectionInvolution,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,Matrix.mul_one,Matrix.one_mul,hp]
    module

theorem projectionInvolution_effect (P : Mat d) (b : Bool) :
    CountProof.symmetryProjection (projectionInvolution P) b=if b then 1-P else P := by
  cases b <;> simp only [CountProof.symmetryProjection,projectionInvolution,Bool.false_eq_true,↓reduceIte] <;> module

end
end Companion.Analytic.TransferProof
