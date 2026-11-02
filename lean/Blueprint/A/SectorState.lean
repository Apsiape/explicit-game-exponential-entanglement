import Blueprint.A.AreaCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Companion.UniformCountTheorem
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace Blueprint.ASector
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

theorem sqrt_residual_bound {d : Nat} (A C : Mat d) (hA : A.PosSemidef) (hC : C.PosSemidef)
    (hAC : A*A≤C) : hs (QIT.psdSqrt C-A)^2≤(C-A*A).trace.re := by
  let S := QIT.psdSqrt C
  have hS := QIT.psdSqrt_pos C
  have hSH : S.conjTranspose=S := hS.isHermitian.eq
  have hSS : S*S=C := QIT.psdSqrt_mul_self_of_posSemidef hC
  have hroot : CFC.sqrt (A*A)=A := CFC.sqrt_unique (by simp [sq]) hA.nonneg
  have hle : A≤S := by
    have hh := CFC.sqrt_le_sqrt (A*A) C hAC
    rwa [hroot] at hh
  have hD : (S-A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hle)
  have hpos := TransferProof.psd_trace_mul_nonneg (S-A) A hD hA
  have heq : hs (S-A)^2=(C-A*A).trace.re-2*((S-A)*A).trace.re := by
    rw [hs_eq_hsNorm,hsNorm_sq,hsSquared_trace,Matrix.conjTranspose_sub,
      hSH,hA.isHermitian.eq]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,hSS]
    rw [Matrix.trace_mul_comm A S]
    ring
  change hs (S-A)^2≤_
  rw [heq]
  linarith

theorem sector_state {d : Nat} (s : State d) (J : Mat d) (hJ : IsInvolution J)
    (hp : 0<((signProjection J true)*s.rho).trace.re) :
    ∃ t : State d, t.rho=(((signProjection J true)*s.rho).trace.re:ℂ)⁻¹ •
      (signProjection J true*s.rho*signProjection J true) ∧
      hs (t.xi-((Real.sqrt ((signProjection J true*s.rho).trace.re))⁻¹:ℂ) •
        (signProjection J true*s.xi*signProjection J true))≤
      hs (signProjection J false*s.xi*signProjection J true)/Real.sqrt ((signProjection J true*s.rho).trace.re) := by
  let P := signProjection J true
  let Q := signProjection J false
  let p := (P*s.rho).trace.re
  let A := P*s.xi*P
  let B := Q*s.xi*P
  let C := P*s.rho*P
  have hPH : P.conjTranspose=P := CountProof.symmetryProjection_hermitian J hJ.1 true
  have hQH : Q.conjTranspose=Q := CountProof.symmetryProjection_hermitian J hJ.1 false
  have hP2 : P*P=P := CountProof.symmetryProjection_square J hJ.2 true
  have hQ2 : Q*Q=Q := CountProof.symmetryProjection_square J hJ.2 false
  have hQP : Q=1-P := by
    simp only [Q,P,signProjection,Bool.false_eq_true,↓reduceIte]
    module
  have hA : A.PosSemidef := by
    simpa only [hPH] using s.xi_positive.mul_mul_conjTranspose_same P
  have hC : C.PosSemidef := by
    simpa only [hPH] using s.positive.mul_mul_conjTranspose_same P
  have hAA : A*A=P*s.xi*P*s.xi*P := by
    calc
      _=P*s.xi*(P*P)*s.xi*P := by simp only [A,Matrix.mul_assoc]
      _=_ := by rw [hP2]
  have hBB : B.conjTranspose*B=P*s.xi*Q*s.xi*P := by
    simp only [B,Matrix.conjTranspose_mul,hPH,hQH,s.xi_positive.isHermitian.eq]
    calc
      _=P*s.xi*(Q*Q)*s.xi*P := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hQ2]
  have hdiff : C-A*A=B.conjTranspose*B := by
    rw [hAA,hBB,hQP]
    dsimp [C]
    rw [←s.xi_square]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
  have hAC : A*A≤C := by
    apply sub_nonneg.mp
    apply Matrix.nonneg_iff_posSemidef.mpr
    rw [hdiff]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  have hres : hs (QIT.psdSqrt C-A)≤hs B := by
    have hh := sqrt_residual_bound A C hA hC hAC
    rw [hdiff,←hsSquared_trace,←hsNorm_sq] at hh
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp hh
  have ht : C.trace=(p:ℂ) := by
    have heq : C.trace=(P*s.rho).trace := by
      change (P*s.rho*P).trace=_
      rw [Matrix.trace_mul_cycle,hP2]
    apply Complex.ext
    · simpa only [Complex.ofReal_re,p] using congrArg Complex.re heq
    · simpa only [Complex.ofReal_im,Complex.zero_im] using hC.trace_nonneg.2.symm
  let t : State d := State.ofQuAIR {
    matrix := ((p:ℂ)⁻¹) • C
    pos := hC.smul (by exact_mod_cast (inv_nonneg.mpr hp.le : (0:ℝ)≤p⁻¹))
    trace_eq_one := by
      rw [Matrix.trace_smul,ht,smul_eq_mul]
      exact inv_mul_cancel₀ (by exact_mod_cast hp.ne' : (p:ℂ)≠0) }
  refine ⟨t,rfl,?_⟩
  have hxi : t.xi=((Real.sqrt p)⁻¹:ℂ) • QIT.psdSqrt C := by
    change QIT.psdSqrt (((p:ℂ)⁻¹) • C)=_
    simpa only [Real.sqrt_inv,Complex.ofReal_inv] using
      QIT.psdSqrt_real_smul (inv_nonneg.mpr hp.le : (0:ℝ)≤p⁻¹) hC
  change hs (t.xi-((Real.sqrt p)⁻¹:ℂ) • A)≤hs B/Real.sqrt p
  rw [hxi,←smul_sub,hs_eq_hsNorm,CountProof.hs_smul]
  simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg p)]
  rw [div_eq_mul_inv,mul_comm (hs B)]
  exact mul_le_mul_of_nonneg_left hres (inv_nonneg.mpr (Real.sqrt_nonneg p))

end
end Blueprint.ASector

#print axioms Blueprint.ASector.sqrt_residual_bound
#print axioms Blueprint.ASector.sector_state
