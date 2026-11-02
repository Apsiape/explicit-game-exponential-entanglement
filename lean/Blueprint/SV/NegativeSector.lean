import Blueprint.SV.SectorVisibility
import Blueprint.RatesDefinitions

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem rounded_pair_bound {d : Nat} (U W xi : Mat d) (hU : IsUnitary U) (hW : IsUnitary W) :
    hs (comm U (roundUnitary W)*xi)≤hs (comm U W*xi)+
      2*hs ((roundUnitary W-W)*xi)+2*hs (comm U xi) := by
  let J := roundUnitary W
  have hJ : IsUnitary J := CountProof.involution_unitary J (ReturnProof.roundUnitary_involution W)
  have he : comm U J*xi=comm U W*xi+U*((J-W)*xi)-(J-W)*U*xi := by
    simp only [Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have h1 := CountProof.hs_sub_le (comm U W*xi+U*((J-W)*xi)) ((J-W)*U*xi)
  have h2 := hsNorm_add_le (comm U W*xi) (U*((J-W)*xi))
  rw [←he] at h1
  rw [hsNorm_unitary_left _ _ hU.1] at h2
  have h3 := ReturnProof.unitary_difference_right_transport J W U xi hJ hW hU
  simp only [hs_eq_hsNorm] at *
  linarith

theorem negative_sector_model {d : Nat} (hd : 0<d) (U : Nat → Mat d) (s : State d) (b : ℝ)
    (hb : 0≤b) (hsmall : b≤1/5) (hU : ∀ j, IsUnitary (U j))
    (hr : ∀ r∈kRelators, hs ((wordEval U r-1)*s.xi)≤b)
    (hc : ∀ j, 1≤j → j≤5 → hs (comm (U j) s.xi)≤b)
    (hcentral : ∀ j, 1≤j → j≤5 → hs (comm (U j) (U 3)*s.xi)≤5*b)
    (hv : 1-3/2*b≤hs ((U 3-1)*s.xi)) :
    ∃ t : State d, kModel U t (60*b) := by
  let W := U 3
  let J := roundUnitary W
  have hJ : IsInvolution J := ReturnProof.roundUnitary_involution W
  have hW : IsUnitary W := hU 3
  have hsq : hs ((W*W-1)*s.xi)≤b := by
    have h := hr [(3,true),(3,true)] (by simp [kRelators])
    simpa [W,wordEval] using h
  have hdiff : hs ((J-W)*s.xi)≤b := (ReturnProof.rounding_weighted_bound W hW s.xi).trans hsq
  have hcJ : hs (comm J s.xi)≤3*b := by
    have h := ReturnProof.rounding_commutator_bound W s.xi hW s.xi_positive.isHermitian
    have hcw := hc 3 (by decide) (by decide)
    change hs (comm W s.xi)≤b at hcw
    simp only [←hs_eq_hsNorm] at h
    linarith
  have hvis : 1/2≤hs ((J-1)*s.xi) := by
    have h := hsNorm_add_le ((W-J)*s.xi) ((J-1)*s.xi)
    have he : (W-J)*s.xi+(J-1)*s.xi=(W-1)*s.xi := by
      simp only [Matrix.sub_mul]
      abel
    have hrev : hsNorm ((W-J)*s.xi)=hsNorm ((J-W)*s.xi) := by
      rw [Matrix.sub_mul,CountProof.hs_sub_rev,←Matrix.sub_mul]
    rw [he,hrev] at h
    change 1-3/2*b≤hs ((W-1)*s.xi) at hv
    simp only [hs_eq_hsNorm] at *
    linarith
  obtain ⟨hp,hq⟩ := sector_probability_lower s J hJ hvis
  have hp0 : 0<(signProjection J true*s.rho).trace.re := by linarith
  obtain ⟨t,ht⟩ := sector_approximation s J hJ hp0
  let q := Real.sqrt (signProjection J true*s.rho).trace.re
  change 1/4≤q at hq
  have hq0 : 0<q := Real.sqrt_pos.mpr hp0
  have hdiv (a : ℝ) (ha : 0≤a) : a/q≤4*a := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith
  refine ⟨t,hU,?_,?_,?_⟩
  · intro r hmem
    have hnorm : ‖wordEval U r-1‖≤2 := difference_operator_norm hd (wordEval U r) 1
      (wordEval_unitary U hU r) (by simp [IsUnitary])
    have h := sector_weighted_bound s t J hJ hp0 ht (wordEval U r-1)
    have hmul := mul_le_mul_of_nonneg_right hnorm (hsNorm_nonneg (comm J s.xi))
    change ‖wordEval U r-1‖*hs (comm J s.xi)≤2*hs (comm J s.xi) at hmul
    have hnum : hs ((wordEval U r-1)*s.xi)+‖wordEval U r-1‖*hs (comm J s.xi)≤7*b := by
      have hrel := hr r hmem
      linarith
    have htop := div_le_div_of_nonneg_right hnum hq0.le
    have hcut := hdiv (7*b) (by positivity)
    exact h.trans (htop.trans (hcut.trans (by nlinarith)))
  · intro j hj1 hj5
    have hpair : hs (comm (U j) J*s.xi)≤9*b := by
      have h := rounded_pair_bound (U j) W s.xi (hU j) hW
      have hcent := hcentral j hj1 hj5
      have hcj := hc j hj1 hj5
      change hs (comm (U j) W*s.xi)≤5*b at hcent
      change hs (comm (U j) J*s.xi)≤_
      linarith
    have h := sector_commutator_bound s t (U j) J (hU j) hJ hp0 ht
    have hcj := hc j hj1 hj5
    have hnum : hs (comm (U j) J*s.xi)+2*hs (comm (U j) s.xi)+hs (comm J s.xi)≤14*b := by
      linarith
    have htop := div_le_div_of_nonneg_right hnum hq0.le
    have hcut := hdiv (14*b) (by positivity)
    exact h.trans (htop.trans (hcut.trans (by nlinarith)))
  · have hdif : hs ((W-J)*s.xi)≤b := by
      rw [Matrix.sub_mul,hs_eq_hsNorm,CountProof.hs_sub_rev,←Matrix.sub_mul,←hs_eq_hsNorm]
      exact hdiff
    have h := sector_marker_bound hd s t W J hW hJ hp0 ht
    have hnum : hs ((W-J)*s.xi)+3*hs (comm J s.xi)≤10*b := by linarith
    have htop := div_le_div_of_nonneg_right hnum hq0.le
    have hcut := hdiv (10*b) (by positivity)
    exact h.trans (htop.trans (hcut.trans (by nlinarith)))

end
end Blueprint.SV

#print axioms Blueprint.SV.rounded_pair_bound
#print axioms Blueprint.SV.negative_sector_model
