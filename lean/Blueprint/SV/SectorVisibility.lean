import Blueprint.SV.SectorCommutators

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem sector_probability {d : Nat} (s : State d) (J : Mat d) (hJ : IsInvolution J) :
    hs ((J-1)*s.xi)^2=4*(signProjection J true*s.rho).trace.re := by
  let P := signProjection J true
  have hPH : P.conjTranspose=P := CountProof.symmetryProjection_hermitian J hJ.1 true
  have hP2 : P*P=P := CountProof.symmetryProjection_square J hJ.2 true
  have he : (J-1)*s.xi=(-2:ℂ) • (P*s.xi) := by
    dsimp [P,signProjection]
    simp only [↓reduceIte,Matrix.smul_mul,Matrix.add_mul,Matrix.neg_mul,Matrix.one_mul,Matrix.sub_mul]
    module
  have hnorm : hs (P*s.xi)^2=(P*s.rho).trace.re := by
    rw [hs_eq_hsNorm,hsNorm_sq,hsSquared_trace,Matrix.conjTranspose_mul,hPH,s.xi_positive.isHermitian.eq]
    have htrace : (s.xi*P*(P*s.xi)).trace=(P*s.rho).trace := by
      calc
        _ = (s.xi*(P*P)*s.xi).trace := by simp only [Matrix.mul_assoc]
        _ = (s.xi*(P*s.xi)).trace := by rw [hP2,Matrix.mul_assoc]
        _ = (P*s.xi*s.xi).trace := Matrix.trace_mul_comm _ _
        _ = (P*s.rho).trace := by rw [Matrix.mul_assoc,s.xi_square]
    rw [htrace]
  rw [he,hs_eq_hsNorm,CountProof.hs_smul]
  norm_num
  rw [mul_pow,←hs_eq_hsNorm,hnorm]
  norm_num
  rfl

theorem sector_probability_lower {d : Nat} (s : State d) (J : Mat d) (hJ : IsInvolution J)
    (hv : 1/2≤hs ((J-1)*s.xi)) :
    1/16≤(signProjection J true*s.rho).trace.re ∧
      1/4≤Real.sqrt (signProjection J true*s.rho).trace.re := by
  have he := sector_probability s J hJ
  have hp : 1/16≤(signProjection J true*s.rho).trace.re := by nlinarith
  refine ⟨hp,?_⟩
  have hp0 : 0≤(signProjection J true*s.rho).trace.re := by linarith
  nlinarith [Real.sq_sqrt hp0,Real.sqrt_nonneg (signProjection J true*s.rho).trace.re]

theorem sector_marker_bound {d : Nat} (hd : 0<d) (s t : State d) (W J : Mat d)
    (hW : IsUnitary W) (hJ : IsInvolution J)
    (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : hs (t.xi-((Real.sqrt (signProjection J true*s.rho).trace.re)⁻¹:ℂ) •
      (signProjection J true*s.xi*signProjection J true))≤
      hs (comm J s.xi)/(2*Real.sqrt (signProjection J true*s.rho).trace.re)) :
    hs ((W+1)*t.xi)≤(hs ((W-J)*s.xi)+3*hs (comm J s.xi))/
      Real.sqrt (signProjection J true*s.rho).trace.re := by
  let P := signProjection J true
  let q := Real.sqrt (P*s.rho).trace.re
  let c : ℂ := (q:ℂ)⁻¹
  let D := t.xi-c • (P*s.xi*P)
  have hq : 0<q := Real.sqrt_pos.mpr hp
  have hn : ‖W-J‖≤2 := difference_operator_norm hd W J hW (CountProof.involution_unitary J hJ)
  have hneg : IsUnitary (-1:Mat d) := by simp [IsUnitary]
  have hnJ : ‖J+1‖≤2 := by simpa only [sub_neg_eq_add] using
    difference_operator_norm hd J (-1) (CountProof.involution_unitary J hJ) hneg
  have h1 := sector_weighted_bound s t J hJ hp ht (W-J)
  have h2 := mul_le_mul_of_nonneg_right hn (hsNorm_nonneg (comm J s.xi))
  change ‖W-J‖*hs (comm J s.xi)≤2*hs (comm J s.xi) at h2
  have h3 : hs ((W-J)*t.xi)≤(hs ((W-J)*s.xi)+2*hs (comm J s.xi))/q := by
    apply h1.trans
    exact div_le_div_of_nonneg_right (add_le_add le_rfl h2) hq.le
  have hJP : (J+1)*P=0 := by
    dsimp [P,signProjection]
    simp only [↓reduceIte,Matrix.mul_smul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_neg,
      Matrix.mul_one,Matrix.one_mul,hJ.2]
    module
  have he : (J+1)*t.xi=(J+1)*D := by
    dsimp [D]
    rw [Matrix.mul_sub,Matrix.mul_smul,←Matrix.mul_assoc,←Matrix.mul_assoc,hJP,
      Matrix.zero_mul,Matrix.zero_mul,smul_zero,sub_zero]
  have h4 := ReturnProof.operator_mul_hs_bound (J+1) D
  have h5 := mul_le_mul_of_nonneg_right hnJ (hsNorm_nonneg D)
  change hs D≤hs (comm J s.xi)/(2*q) at ht
  have h6 : hs ((J+1)*t.xi)≤hs (comm J s.xi)/q := by
    rw [he]
    have h7 := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2)
    have h8 : 2*(hs (comm J s.xi)/(2*q))=hs (comm J s.xi)/q := by ring
    simp only [hs_eq_hsNorm] at *
    linarith
  have h7 := hsNorm_add_le ((W-J)*t.xi) ((J+1)*t.xi)
  have hsum : (W-J)*t.xi+(J+1)*t.xi=(W+1)*t.xi := by
    simp only [Matrix.sub_mul,Matrix.add_mul]
    abel
  rw [hsum] at h7
  change hs ((W+1)*t.xi)≤(hs ((W-J)*s.xi)+3*hs (comm J s.xi))/q
  have heq : (hs ((W-J)*s.xi)+2*hs (comm J s.xi))/q+hs (comm J s.xi)/q=
      (hs ((W-J)*s.xi)+3*hs (comm J s.xi))/q := by ring
  rw [←heq]
  simp only [hs_eq_hsNorm] at *
  linarith

end
end Blueprint.SV

#print axioms Blueprint.SV.sector_probability
#print axioms Blueprint.SV.sector_probability_lower
#print axioms Blueprint.SV.sector_marker_bound
