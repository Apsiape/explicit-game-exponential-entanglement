import Blueprint.RatesDefinitions
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem generic_psd_trace {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Matrix α α ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0≤(A*B).trace.re := by
  let S := QIT.psdSqrt A
  have hS : S.conjTranspose=S := QIT.psdSqrt_isHermitian A
  have hSS : S*S=A := QIT.psdSqrt_mul_self_of_posSemidef hA
  have hp : (S*B*S).PosSemidef := by
    simpa only [hS] using hB.mul_mul_conjTranspose_same S
  have he : (A*B).trace=(S*B*S).trace := by
    calc
      _=((S*S)*B).trace := by rw [hSS]
      _=_ := (Matrix.trace_mul_cycle S B S).symm
  rw [he]
  exact hp.trace_nonneg.1

theorem generic_isometry_complement {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (V : Matrix α β ℂ) (hV : V.conjTranspose*V=1) :
    (1-V*V.conjTranspose).PosSemidef := by
  let P := 1-V*V.conjTranspose
  have hh : P.conjTranspose=P := by simp [P,Matrix.conjTranspose_mul]
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

theorem generic_isometry_right_le {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (A : Matrix α β ℂ) (V : Matrix β γ ℂ)
    (hV : V.conjTranspose*V=1) : hsNorm (A*V)≤hsNorm A := by
  have h := generic_psd_trace (A.conjTranspose*A) (1-V*V.conjTranspose)
    (Matrix.posSemidef_conjTranspose_mul_self A) (generic_isometry_complement V hV)
  have ht : ((A*V).conjTranspose*(A*V)).trace=(A.conjTranspose*A*(V*V.conjTranspose)).trace := by
    rw [Matrix.conjTranspose_mul]
    calc
      _=(V.conjTranspose*(A.conjTranspose*A*V)).trace := by simp only [Matrix.mul_assoc]
      _=((A.conjTranspose*A*V)*V.conjTranspose).trace := Matrix.trace_mul_comm _ _
      _=_ := by simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_sub,Matrix.mul_one,Matrix.trace_sub,Complex.sub_re] at h
  rw [←ht,←hsSquared_trace,←hsSquared_trace,←hsNorm_sq,←hsNorm_sq] at h
  nlinarith [hsNorm_nonneg (A*V),hsNorm_nonneg A]

theorem hs_fromCols_zero {a b : Nat} (A : Matrix (Fin a) (Fin b) ℂ) (c : Nat) :
    hsNorm (Matrix.fromCols A (0:Matrix (Fin a) (Fin c) ℂ))=hsNorm A := by
  simp [hsNorm,hsSquared,Fintype.sum_sum_type]

theorem rectangular_consistency_squared {a b : Nat} (psi : Matrix (Fin a) (Fin b) ℂ)
    (xi : Mat a) (hxi : xi.PosSemidef) (hgram : xi*xi=psi*psi.conjTranspose)
    (A : Mat a) (B : Mat b) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hs (comm A xi)^2≤2*hs (A*psi-psi*B)^2 := by
  let P := Matrix.fromCols psi (0:Mat a)
  let T := Matrix.fromBlocks B (0:Matrix (Fin b) (Fin a) ℂ) 0 (0:Mat a)
  have hP : xi*xi.conjTranspose=P*P.conjTranspose := by
    simp only [P,Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.conjTranspose_zero,Matrix.fromCols_mul_fromRows,Matrix.zero_mul,add_zero,hxi.isHermitian.eq]
    exact hgram
  obtain ⟨V,hfactor⟩ := QIT.ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq xi P hP
    (by simp only [Fintype.card_fin,Fintype.card_sum]; omega)
  let W := V.matrix.transpose
  have hW : W*W.conjTranspose=1 := TransferProof.transpose_isometry_coisometry _ V.isometry
  have hTH : T.IsHermitian := by
    simp only [T,Matrix.IsHermitian,Matrix.fromBlocks_conjTranspose,hB.eq,Matrix.conjTranspose_zero]
  have hH : (W*T*W.conjTranspose).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose W hTH
  have hcons := consistency_squared (W*T*W.conjTranspose) A xi hH hA hxi
  have he : (A*P-P*T)*W.conjTranspose=A*xi-xi*(W*T*W.conjTranspose) := by
    rw [hfactor,Matrix.sub_mul]
    change (A*(xi*W))*W.conjTranspose-((xi*W)*T)*W.conjTranspose=_
    calc
      _=(A*xi)*(W*W.conjTranspose)-xi*(W*T*W.conjTranspose) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hW,Matrix.mul_one]
  have herr := generic_isometry_right_le (A*P-P*T) W.conjTranspose
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hW)
  rw [he] at herr
  have hpad : A*P-P*T=Matrix.fromCols (A*psi-psi*B) (0:Mat a) := by
    simp only [P,T,Matrix.mul_fromCols,Matrix.fromCols_mul_fromBlocks,
      Matrix.mul_zero,Matrix.zero_mul,add_zero]
    ext i j
    cases j <;> simp
  rw [hpad,hs_fromCols_zero] at herr
  have hsq := pow_le_pow_left₀ (hsNorm_nonneg _) herr 2
  simp only [←hs_eq_hsNorm] at *
  exact hcons.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))

theorem alice_weighted_norm {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (s : State a) (hrho : s.rho=(psi.conjTranspose*psi).transpose) (A : Mat a) :
    hs (A*s.xi)=hs (psi*A.transpose) := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  simp only [hs_eq_hsNorm,hsNorm_sq,hsSquared_trace]
  have hleft : ((A*s.xi).conjTranspose*(A*s.xi)).trace=
      (A.conjTranspose*A*s.rho).trace := by
    simp only [Matrix.conjTranspose_mul,s.xi_positive.isHermitian.eq]
    calc
      _=(s.xi*(A.conjTranspose*A*s.xi)).trace := by noncomm_ring
      _=((A.conjTranspose*A*s.xi)*s.xi).trace := Matrix.trace_mul_comm _ _
      _=_ := by rw [Matrix.mul_assoc,s.xi_square]
  rw [hleft,hrho]
  have hright : ((psi*A.transpose).conjTranspose*(psi*A.transpose)).trace=
      (A.conjTranspose*A*(psi.conjTranspose*psi).transpose).trace := by
    rw [Matrix.conjTranspose_mul]
    calc
      _=(A.transpose.conjTranspose*(psi.conjTranspose*psi)*A.transpose).trace := by
        simp only [Matrix.mul_assoc]
      _=((A.transpose.conjTranspose*(psi.conjTranspose*psi)*A.transpose).transpose).trace :=
        (Matrix.trace_transpose _).symm
      _=(A*(psi.conjTranspose*psi).transpose*A.conjTranspose).trace := by
        simp only [Matrix.transpose_mul,Matrix.transpose_transpose,
          ←Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,Matrix.mul_assoc]
      _=(A.conjTranspose*A*(psi.conjTranspose*psi).transpose).trace := by
        rw [Matrix.trace_mul_cycle]
  rw [hright]

end
end Blueprint.W2
