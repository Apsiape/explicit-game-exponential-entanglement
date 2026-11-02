import Companion.ProjectiveFunctions

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem isometry_complement_positive {d r : Nat} (V : Matrix (Fin d) (Fin r) ℂ)
    (hV : V.conjTranspose*V=1) : (1-V*V.conjTranspose).PosSemidef := by
  let P := 1-V*V.conjTranspose
  have hh : P.conjTranspose=P := by
    simp only [P,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have hm : (V*V.conjTranspose)*(V*V.conjTranspose)=V*V.conjTranspose := by
    calc
      _=V*(V.conjTranspose*V)*V.conjTranspose := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hV,Matrix.mul_one]
  have hp : P*P=P := by
    simp only [P,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hm]
    abel
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rw [hh,hp] at h
  exact h

theorem hsNorm_isometry_right_le {a d r : Nat} (A : Matrix (Fin a) (Fin d) ℂ)
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1) : hsNorm (A*V)≤hsNorm A := by
  have h := psd_trace_mul_nonneg (A.conjTranspose*A) (1-V*V.conjTranspose)
    (Matrix.posSemidef_conjTranspose_mul_self A) (isometry_complement_positive V hV)
  have ht : ((A*V).conjTranspose*(A*V)).trace=(A.conjTranspose*A*(V*V.conjTranspose)).trace := by
    rw [Matrix.conjTranspose_mul]
    calc
      _=(V.conjTranspose*(A.conjTranspose*A*V)).trace := by simp only [Matrix.mul_assoc]
      _=((A.conjTranspose*A*V)*V.conjTranspose).trace := Matrix.trace_mul_comm _ _
      _=_ := by simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_sub,Matrix.mul_one,Matrix.trace_sub,Complex.sub_re] at h
  rw [← ht,← hsSquared_trace,← hsSquared_trace,← hsNorm_sq,← hsNorm_sq] at h
  nlinarith [hsNorm_nonneg (A*V),hsNorm_nonneg A]

/-- Rectangular Schmidt/polar factorization on a full Bob support. The
coisometry is a concrete matrix, obtained from equal Gram matrices. -/
theorem schmidt_polar_factor {dA r : Nat} (psi : Matrix (Fin r) (Fin dA) ℂ)
    (hpd : (psi*psi.conjTranspose).PosDef) :
    ∃ W : Matrix (Fin r) (Fin dA) ℂ, W*W.conjTranspose=1 ∧
      psi=QIT.psdSqrt (psi*psi.conjTranspose)*W := by
  let xi := QIT.psdSqrt (psi*psi.conjTranspose)
  have hfull : (psi*psi.conjTranspose).rank=r := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit _ hpd.isUnit
  have hcard : r≤dA := by
    rw [Matrix.rank_self_mul_conjTranspose] at hfull
    exact hfull.symm.trans_le psi.rank_le_width
  have hxi : xi.conjTranspose=xi := QIT.psdSqrt_isHermitian _
  have hg : xi*xi.conjTranspose=psi*psi.conjTranspose := by
    rw [hxi]
    exact QIT.psdSqrt_mul_self_of_posSemidef hpd.posSemidef
  obtain ⟨V,hV⟩ := QIT.ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq xi psi hg
    (by simpa only [Fintype.card_fin] using hcard)
  exact ⟨V.matrix.transpose,transpose_isometry_coisometry V.matrix V.isometry,hV⟩

theorem polar_weighted_norm {dA r : Nat} (psi : Matrix (Fin r) (Fin dA) ℂ)
    (xi : Mat r) (W : Matrix (Fin r) (Fin dA) ℂ) (hW : W*W.conjTranspose=1)
    (hp : psi=xi*W) (T : Mat r) : hsNorm (T*xi)=hsNorm (T*psi) := by
  rw [hp,← Matrix.mul_assoc,hsNorm_coisometry_right _ _ hW]

theorem polar_standard_form_error {dA r : Nat} (psi : Matrix (Fin r) (Fin dA) ℂ)
    (xi : Mat r) (W : Matrix (Fin r) (Fin dA) ℂ) (hW : W*W.conjTranspose=1)
    (hp : psi=xi*W) (A : Mat dA) (B : Mat r) :
    hsNorm (B*xi-xi*(W*A*W.conjTranspose))≤hsNorm (B*psi-psi*A) := by
  have he : (B*psi-psi*A)*W.conjTranspose=B*xi-xi*(W*A*W.conjTranspose) := by
    rw [hp,Matrix.sub_mul]
    have hh : (B*(xi*W))*W.conjTranspose=B*xi := by
      calc
        _=(B*xi)*(W*W.conjTranspose) := by simp only [Matrix.mul_assoc]
        _=_ := by rw [hW,Matrix.mul_one]
    rw [hh]
    simp only [Matrix.mul_assoc]
  have h := hsNorm_isometry_right_le (B*psi-psi*A) W.conjTranspose (by
    simpa only [Matrix.conjTranspose_conjTranspose] using hW)
  rw [he] at h
  exact h

/-- The stated sqrt(2) state-commutator estimate, now for arbitrary
rectangular purification matrices with full Bob support. -/
theorem rectangular_consistency {dA r : Nat} (psi : Matrix (Fin r) (Fin dA) ℂ)
    (hpd : (psi*psi.conjTranspose).PosDef) (A : Mat dA) (B : Mat r)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hsNorm (comm B (QIT.psdSqrt (psi*psi.conjTranspose)))≤
      Real.sqrt 2*hsNorm (B*psi-psi*A) := by
  obtain ⟨W,hW,hp⟩ := schmidt_polar_factor psi hpd
  have hh : (W*A*W.conjTranspose).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose W hA
  have hc := consistency (W*A*W.conjTranspose) B (QIT.psdSqrt (psi*psi.conjTranspose))
    hh hB (QIT.psdSqrt_pos _)
  have he := polar_standard_form_error psi _ W hW hp A B
  exact hc.trans (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _))

end
end Companion.Analytic.TransferProof
