import Blueprint.A.SectorState
import Companion.BranchComposition

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem projection_hs_left {d : Nat} (J A : Mat d) (hJ : IsInvolution J) (b : Bool) :
    hs (signProjection J b*A)≤hs A :=
  (sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
    (ReturnProof.binary_branch_le J A hJ b)

theorem projection_hs_right {d : Nat} (J A : Mat d) (hJ : IsInvolution J) (b : Bool) :
    hs (A*signProjection J b)≤hs A := by
  have hPH : (signProjection J b).conjTranspose=signProjection J b :=
    CountProof.symmetryProjection_hermitian J hJ.1 b
  rw [hs_eq_hsNorm,←hsNorm_conjTranspose (A*signProjection J b),Matrix.conjTranspose_mul,hPH]
  exact (projection_hs_left J A.conjTranspose hJ b).trans_eq (hsNorm_conjTranspose A)

theorem projection_commutator_hs {d : Nat} (J xi : Mat d) :
    hs (comm (signProjection J true) xi)=hs (comm J xi)/2 := by
  have he : comm (signProjection J true) xi=(-1/2:ℂ) • comm J xi := by
    simp only [signProjection,↓reduceIte,Analytic.comm,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.add_mul,Matrix.mul_add,Matrix.neg_mul,Matrix.mul_neg,Matrix.one_mul,Matrix.mul_one]
    module
  rw [he,hs_eq_hsNorm,CountProof.hs_smul,hs_eq_hsNorm]
  norm_num
  ring

theorem off_diagonal_hs {d : Nat} (J xi : Mat d) (hJ : IsInvolution J) :
    hs (signProjection J false*xi*signProjection J true)≤hs (comm J xi)/2 := by
  let P := signProjection J true
  let Q := signProjection J false
  have hQP : Q*P=0 := by
    exact CountProof.symmetryProjection_mul J hJ.2 false true
  have he : Q*xi*P= -(Q*comm P xi) := by
    simp only [Analytic.comm,Matrix.mul_sub,←Matrix.mul_assoc,hQP,Matrix.zero_mul]
    abel
  rw [he,hs_eq_hsNorm,CountProof.hs_neg]
  exact (projection_hs_left J (comm P xi) hJ false).trans_eq
    (projection_commutator_hs J xi)

theorem unitary_operator_norm {d : Nat} (hd : 0<d) (U : Mat d) (hU : IsUnitary U) :
    ‖U‖=1 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact CStarRing.norm_coe_unitary (asUnitary U hU)

theorem difference_operator_norm {d : Nat} (hd : 0<d) (U V : Mat d)
    (hU : IsUnitary U) (hV : IsUnitary V) : ‖U-V‖≤2 := by
  have h := norm_sub_le U V
  rw [unitary_operator_norm hd U hU,unitary_operator_norm hd V hV] at h
  norm_num at h ⊢
  exact h

theorem sector_approximation {d : Nat} (s : State d) (J : Mat d) (hJ : IsInvolution J)
    (hp : 0<(signProjection J true*s.rho).trace.re) :
    ∃ t : State d,
      hs (t.xi-((Real.sqrt (signProjection J true*s.rho).trace.re)⁻¹:ℂ) •
        (signProjection J true*s.xi*signProjection J true))≤
        hs (comm J s.xi)/(2*Real.sqrt (signProjection J true*s.rho).trace.re) := by
  obtain ⟨t,_,ht⟩ := ASector.sector_state s J hJ hp
  refine ⟨t,ht.trans ?_⟩
  have h := div_le_div_of_nonneg_right (off_diagonal_hs J s.xi hJ)
    (Real.sqrt_nonneg (signProjection J true*s.rho).trace.re)
  convert h using 1 <;> ring

theorem sector_weighted_bound {d : Nat} (s t : State d) (J : Mat d)
    (hJ : IsInvolution J) (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : hs (t.xi-((Real.sqrt (signProjection J true*s.rho).trace.re)⁻¹:ℂ) •
      (signProjection J true*s.xi*signProjection J true))≤
      hs (comm J s.xi)/(2*Real.sqrt (signProjection J true*s.rho).trace.re))
    (A : Mat d) : hs (A*t.xi)≤
      (hs (A*s.xi)+‖A‖*hs (comm J s.xi))/Real.sqrt (signProjection J true*s.rho).trace.re := by
  let P := signProjection J true
  let q := Real.sqrt (P*s.rho).trace.re
  let c : ℂ := (q:ℂ)⁻¹
  have hq : 0<q := Real.sqrt_pos.mpr hp
  have hc : ‖c‖=q⁻¹ := by
    simp only [c,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
  have h1 := hsNorm_add_le (A*(t.xi-c • (P*s.xi*P))) (c • (A*(P*s.xi*P)))
  have he : A*(t.xi-c • (P*s.xi*P))+c • (A*(P*s.xi*P))=A*t.xi := by
    simp only [Matrix.mul_sub,Matrix.mul_smul]
    abel
  rw [he,CountProof.hs_smul,hc] at h1
  have h2 := ReturnProof.operator_mul_hs_bound A (t.xi-c • (P*s.xi*P))
  have hP2 : P*P=P := CountProof.symmetryProjection_square J hJ.2 true
  have he2 : A*(P*s.xi*P)=(A*s.xi)*P+A*comm P s.xi*P := by
    simp only [Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc,hP2]
    abel
  have h3 := hsNorm_add_le ((A*s.xi)*P) (A*comm P s.xi*P)
  rw [←he2] at h3
  have h4 := projection_hs_right J (A*s.xi) hJ true
  have h5 := projection_hs_right J (A*comm P s.xi) hJ true
  change hs (A*s.xi*P)≤hs (A*s.xi) at h4
  change hs (A*comm P s.xi*P)≤hs (A*comm P s.xi) at h5
  have h6 := ReturnProof.operator_mul_hs_bound A (comm P s.xi)
  have hpcomm := projection_commutator_hs J s.xi
  change hs (comm P s.xi)=hs (comm J s.xi)/2 at hpcomm
  rw [←hs_eq_hsNorm,←hs_eq_hsNorm,hpcomm] at h6
  have h7 : hs (A*(P*s.xi*P))≤hs (A*s.xi)+‖A‖*(hs (comm J s.xi)/2) := by
    simp only [hs_eq_hsNorm] at *
    linarith
  change hs (t.xi-c • (P*s.xi*P))≤hs (comm J s.xi)/(2*q) at ht
  change hs (A*t.xi)≤(hs (A*s.xi)+‖A‖*hs (comm J s.xi))/q
  have h8 := mul_le_mul_of_nonneg_left ht (norm_nonneg A)
  have h9 := mul_le_mul_of_nonneg_left h7 (inv_nonneg.mpr hq.le)
  have heq : ‖A‖*(hs (comm J s.xi)/(2*q))+
      q⁻¹*(hs (A*s.xi)+‖A‖*(hs (comm J s.xi)/2))=
      (hs (A*s.xi)+‖A‖*hs (comm J s.xi))/q := by field_simp; ring
  rw [←heq]
  simp only [hs_eq_hsNorm] at *
  linarith

end
end Blueprint.SV

#print axioms Blueprint.SV.projection_hs_left
#print axioms Blueprint.SV.projection_hs_right
#print axioms Blueprint.SV.projection_commutator_hs
#print axioms Blueprint.SV.off_diagonal_hs
#print axioms Blueprint.SV.unitary_operator_norm
#print axioms Blueprint.SV.difference_operator_norm
#print axioms Blueprint.SV.sector_approximation
#print axioms Blueprint.SV.sector_weighted_bound
