import Blueprint.SV.SectorEstimates
import Blueprint.AWordArea

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem projection_pair_hs {d : Nat} (U J xi : Mat d) :
    hs (comm U (signProjection J true)*xi)=hs (comm U J*xi)/2 := by
  have he : comm U (signProjection J true)*xi=(-1/2:ℂ) • (comm U J*xi) := by
    simp only [signProjection,↓reduceIte,Analytic.comm,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.add_mul,Matrix.mul_add,Matrix.neg_mul,Matrix.mul_neg,Matrix.one_mul,Matrix.mul_one,
      Matrix.sub_mul,Matrix.mul_assoc]
    module
  rw [he,hs_eq_hsNorm,CountProof.hs_smul,hs_eq_hsNorm]
  norm_num
  ring

theorem adjoint_pair_hs {d : Nat} (U J xi : Mat d) (hU : IsUnitary U) (hJ : IsUnitary J) :
    hs (comm U.conjTranspose J*xi)≤hs (comm U J*xi)+2*hs (comm U xi) := by
  have he : comm U.conjTranspose J*xi=
      -(U.conjTranspose*((U*J-J*U)*U.conjTranspose*xi)) := by
    simp only [Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,←Matrix.mul_assoc,hU.1,Matrix.one_mul]
    simp only [Matrix.mul_assoc,hU.2,Matrix.mul_one]
    abel
  rw [he,hs_eq_hsNorm,CountProof.hs_neg,
    hsNorm_unitary_left _ _ (ReturnProof.unitary_adjoint U hU).1]
  have h := ReturnProof.unitary_difference_right_transport (U*J) (J*U) U.conjTranspose xi
    (ReturnProof.unitary_mul U J hU hJ) (ReturnProof.unitary_mul J U hJ hU)
    (ReturnProof.unitary_adjoint U hU)
  rw [←hs_eq_hsNorm,←hs_eq_hsNorm,←hs_eq_hsNorm,AWordArea.adjoint_commutator U xi hU] at h
  exact h

theorem projection_pair_right {d : Nat} (s : State d) (U J : Mat d)
    (hU : IsUnitary U) (hJ : IsInvolution J) :
    hs (s.xi*comm U (signProjection J true))≤hs (comm U J*s.xi)/2+hs (comm U s.xi) := by
  let P := signProjection J true
  have hPH : P.conjTranspose=P := CountProof.symmetryProjection_hermitian J hJ.1 true
  have he : (s.xi*comm U P).conjTranspose= -(comm U.conjTranspose P*s.xi) := by
    simp only [Analytic.comm,Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,hPH,
      s.xi_positive.isHermitian.eq,Matrix.sub_mul]
    abel
  rw [hs_eq_hsNorm,←hsNorm_conjTranspose (s.xi*comm U (signProjection J true))]
  change hsNorm (s.xi*comm U P).conjTranspose≤_
  rw [he,CountProof.hs_neg,←hs_eq_hsNorm]
  rw [show hs (comm U.conjTranspose P*s.xi)=hs (comm U.conjTranspose J*s.xi)/2 from
    projection_pair_hs U.conjTranspose J s.xi]
  have h := adjoint_pair_hs U J s.xi hU (CountProof.involution_unitary J hJ)
  linarith

theorem unitary_state_noise {d : Nat} (U D : Mat d) (hU : IsUnitary U) :
    hs (comm U D)≤2*hs D := by
  have h := CountProof.hs_sub_le (U*D) (D*U)
  rw [hsNorm_unitary_left _ _ hU.1,hsNorm_unitary_right _ _ hU.2] at h
  simpa only [Analytic.comm,hs_eq_hsNorm,two_mul] using h

theorem sector_commutator_bound {d : Nat} (s t : State d) (U J : Mat d)
    (hU : IsUnitary U) (hJ : IsInvolution J)
    (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : hs (t.xi-((Real.sqrt (signProjection J true*s.rho).trace.re)⁻¹:ℂ) •
      (signProjection J true*s.xi*signProjection J true))≤
      hs (comm J s.xi)/(2*Real.sqrt (signProjection J true*s.rho).trace.re)) :
    hs (comm U t.xi)≤(hs (comm U J*s.xi)+2*hs (comm U s.xi)+hs (comm J s.xi))/
      Real.sqrt (signProjection J true*s.rho).trace.re := by
  let P := signProjection J true
  let q := Real.sqrt (P*s.rho).trace.re
  let c : ℂ := (q:ℂ)⁻¹
  let D := t.xi-c • (P*s.xi*P)
  have hq : 0<q := Real.sqrt_pos.mpr hp
  have hc : ‖c‖=q⁻¹ := by
    simp only [c,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
  have he : comm U t.xi=comm U D+c • comm U (P*s.xi*P) := by
    simp only [D,Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,smul_sub]
    abel
  have h1 := hsNorm_add_le (comm U D) (c • comm U (P*s.xi*P))
  rw [←he,CountProof.hs_smul,hc] at h1
  have h2 := unitary_state_noise U D hU
  have he2 : comm U (P*s.xi*P)=comm U P*s.xi*P+P*comm U s.xi*P+P*s.xi*comm U P := by
    simp only [Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
    abel
  have h3 := hsNorm_add_le (comm U P*s.xi*P+P*comm U s.xi*P) (P*s.xi*comm U P)
  have h4 := hsNorm_add_le (comm U P*s.xi*P) (P*comm U s.xi*P)
  rw [←he2] at h3
  have h5 : hs (comm U P*s.xi*P)≤hs (comm U J*s.xi)/2 :=
    (projection_hs_right J (comm U P*s.xi) hJ true).trans_eq (projection_pair_hs U J s.xi)
  have h6 : hs (P*comm U s.xi*P)≤hs (comm U s.xi) :=
    (projection_hs_right J (P*comm U s.xi) hJ true).trans (projection_hs_left J (comm U s.xi) hJ true)
  have h7 : hs (P*s.xi*comm U P)≤hs (comm U J*s.xi)/2+hs (comm U s.xi) := by
    rw [Matrix.mul_assoc]
    exact (projection_hs_left J (s.xi*comm U P) hJ true).trans (projection_pair_right s U J hU hJ)
  have h8 : hs (comm U (P*s.xi*P))≤hs (comm U J*s.xi)+2*hs (comm U s.xi) := by
    simp only [hs_eq_hsNorm] at *
    linarith
  change hs D≤hs (comm J s.xi)/(2*q) at ht
  have h9 := mul_le_mul_of_nonneg_left h8 (inv_nonneg.mpr hq.le)
  have h10 := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2)
  change hs (comm U t.xi)≤(hs (comm U J*s.xi)+2*hs (comm U s.xi)+hs (comm J s.xi))/q
  have heq : 2*(hs (comm J s.xi)/(2*q))+
      q⁻¹*(hs (comm U J*s.xi)+2*hs (comm U s.xi))=
      (hs (comm U J*s.xi)+2*hs (comm U s.xi)+hs (comm J s.xi))/q := by field_simp; ring
  rw [←heq]
  simp only [hs_eq_hsNorm] at *
  linarith

end
end Blueprint.SV

#print axioms Blueprint.SV.projection_pair_hs
#print axioms Blueprint.SV.adjoint_pair_hs
#print axioms Blueprint.SV.projection_pair_right
#print axioms Blueprint.SV.unitary_state_noise
#print axioms Blueprint.SV.sector_commutator_bound
