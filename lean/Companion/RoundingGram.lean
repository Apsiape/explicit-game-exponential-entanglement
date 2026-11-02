import Companion.RoundingSpectrum

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

theorem rounding_polynomial_positive {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    ((4:ℂ) • (1-hermitianPart U*hermitianPart U)-
      (2:ℂ) • (1-roundUnitary U*hermitianPart U)).PosSemidef := by
  let hH := hermitianPart_hermitian U
  let E := hH.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ (Mat d) E
  let lam := hH.eigenvalues
  let D := Matrix.diagonal (fun i => (lam i:ℂ))
  let T := Matrix.diagonal (fun i => (roundingSign (lam i):ℂ))
  let q := fun i => 4*(1-(lam i)^2)-2*(1-roundingSign (lam i)*lam i)
  have hC : C D=hermitianPart U := hH.spectral_theorem.symm
  have hT : C T=roundUnitary U := by
    rw [roundUnitary_eq_cfc,hH.cfc_eq]
    rfl
  have he : (4:ℂ) • (1-D*D)-(2:ℂ) • (1-T*D)=Matrix.diagonal (fun i => (q i:ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [D,T,q,Matrix.diagonal_mul_diagonal,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,
        Matrix.diagonal_apply_eq,smul_eq_mul]
      push_cast
      ring
    · simp [D,T,Matrix.diagonal_mul_diagonal,Matrix.one_apply,hij,Matrix.smul_apply]
  have hq (i : Fin d) : 0≤q i := by
    have hi := hermitianPart_eigenvalues_interval U hU i
    change -1≤lam i ∧ lam i≤1 at hi
    by_cases hx : 0≤lam i
    · have hp := mul_nonneg (sub_nonneg.mpr hi.2) (show 0≤1+2*lam i by linarith)
      dsimp only [q,roundingSign]
      rw [if_pos hx]
      nlinarith
    · have hp := mul_nonneg (show 0≤1+lam i by linarith) (show 0≤1-2*lam i by linarith)
      dsimp only [q,roundingSign]
      rw [if_neg hx]
      nlinarith
  have hp : (Matrix.diagonal (fun i => (q i:ℂ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => by exact_mod_cast hq i)
  have hmap : C ((4:ℂ) • (1-D*D)-(2:ℂ) • (1-T*D))=
      (4:ℂ) • (1-hermitianPart U*hermitianPart U)-(2:ℂ) • (1-roundUnitary U*hermitianPart U) := by
    simp only [map_sub,map_smul,map_one,map_mul,hC,hT]
  rw [← hmap,he]
  exact hp.mul_mul_conjTranspose_same (E:Mat d)

theorem square_defect_gram {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    (U*U-1).conjTranspose*(U*U-1)=(4:ℂ) • (1-hermitianPart U*hermitianPart U) := by
  have hR : (U.conjTranspose*U.conjTranspose)*(U*U)=1 := by
    calc
      _=U.conjTranspose*(U.conjTranspose*U)*U := by simp only [Matrix.mul_assoc]
      _=1 := by rw [hU.1,Matrix.mul_one,hU.1]
  have hG : (U*U-1).conjTranspose*(U*U-1)=(2:ℂ) • (1:Mat d)-U*U-U.conjTranspose*U.conjTranspose := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.conjTranspose_one,
      Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,hR]
    module
  have hH : (4:ℂ) • (hermitianPart U*hermitianPart U)=
      U*U+(2:ℂ) • (1:Mat d)+U.conjTranspose*U.conjTranspose := by
    simp only [hermitianPart,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.add_mul,Matrix.mul_add,hU.1,hU.2]
    module
  rw [hG,smul_sub,hH]
  module

theorem rounded_defect_gram {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    (roundUnitary U-U).conjTranspose*(roundUnitary U-U)=
      (2:ℂ) • (1-roundUnitary U*hermitianPart U) := by
  let B := roundUnitary U
  have hB : IsInvolution B := roundUnitary_involution U
  have hc : B*U=U*B := (roundUnitary_commute U hU).eq
  have hs : U.conjTranspose*B=B*U.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hc
    simpa only [Matrix.conjTranspose_mul,hB.1] using h
  have hG : (B-U).conjTranspose*(B-U)=(2:ℂ) • (1:Mat d)-B*U-U.conjTranspose*B := by
    simp only [Matrix.conjTranspose_sub,hB.1,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_one,Matrix.one_mul,hB.2,hU.1]
    module
  have hH : (2:ℂ) • (B*hermitianPart U)=B*U+U.conjTranspose*B := by
    rw [hs]
    simp only [hermitianPart,Matrix.mul_smul,Matrix.mul_add,smul_smul]
    module
  change (B-U).conjTranspose*(B-U)=(2:ℂ) • (1-B*hermitianPart U)
  rw [hG,smul_sub,hH]
  abel

theorem rounding_gram_positive {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    ((U*U-1).conjTranspose*(U*U-1)-(roundUnitary U-U).conjTranspose*(roundUnitary U-U)).PosSemidef := by
  rw [square_defect_gram U hU,rounded_defect_gram U hU]
  exact rounding_polynomial_positive U hU

/-- Sharp state-weighted rounding estimate. The factor on the right is
one, and the multiplying matrix need not be positive or invertible. -/
theorem rounding_weighted_bound {d n : Nat} (U : Mat d) (hU : IsUnitary U)
    (X : Matrix (Fin d) (Fin n) ℂ) :
    hsNorm ((roundUnitary U-U)*X)≤hsNorm ((U*U-1)*X) := by
  let A := U*U-1
  let B := roundUnitary U-U
  have hp := (rounding_gram_positive U hU).mul_mul_conjTranspose_same X.conjTranspose
  have ht := hp.trace_nonneg.1
  simp only [Matrix.conjTranspose_conjTranspose,Complex.zero_re] at ht
  have he : (X.conjTranspose*(A.conjTranspose*A-B.conjTranspose*B)*X).trace=
      ((A*X).conjTranspose*(A*X)).trace-((B*X).conjTranspose*(B*X)).trace := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  change 0≤(X.conjTranspose*(A.conjTranspose*A-B.conjTranspose*B)*X).trace.re at ht
  rw [he,Complex.sub_re,← hsSquared_trace,← hsSquared_trace,← hsNorm_sq,← hsNorm_sq] at ht
  nlinarith [hsNorm_nonneg (A*X),hsNorm_nonneg (B*X)]

end
end Companion.Analytic.ReturnProof
