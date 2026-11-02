import Blueprint.SV.KCentral
import Blueprint.SV.NegativeSector

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem flat_visible_sector (K : ℝ) (hK : 1≤K)
    (hcentral : ∀ (d : Nat) (U : Nat → Mat d) e, 0≤e →
      normalizedRepresentation kRelators U e → ∀ j, 1≤j → j≤5 →
      normalizedHS (wordEval U (ASector.commWord [(j,true)] [(3,true)])-1)≤K*e)
    (d : Nat) (hd : 0<d) (U : Nat → Mat d) (e delta : ℝ)
    (he : 0<e) (hdelt : 0<delta) (hesmall : e≤delta/2)
    (hr : normalizedRepresentation kRelators U e) (hv : delta≤normalizedHS (U 3-1)) :
    ∃ t : State d, kModel U t (4*(K+2)*e/delta) := by
  let s := MainProof.flatState d hd
  let W := U 3
  let J := roundUnitary W
  have hJ : IsInvolution J := ReturnProof.roundUnitary_involution W
  have hW : IsUnitary W := hr.1 3
  have hflat (A : Mat d) : hs (comm A s.xi)=0 := by
    rw [MainProof.flatState_commutes]
    simp [hs]
  have hrel (r : Word) (hmem : r∈kRelators) : hs ((wordEval U r-1)*s.xi)≤e := by
    rw [MainProof.flatState_weighted_norm]
    exact hr.2 r hmem
  have hsq : hs ((W*W-1)*s.xi)≤e := by
    simpa [W,wordEval] using hrel [(3,true),(3,true)] (by simp [kRelators])
  have hdiff : hs ((J-W)*s.xi)≤e := (ReturnProof.rounding_weighted_bound W hW s.xi).trans hsq
  have hvJ : delta/2≤hs ((J-1)*s.xi) := by
    have ht := hsNorm_add_le ((W-J)*s.xi) ((J-1)*s.xi)
    have heq : (W-J)*s.xi+(J-1)*s.xi=(W-1)*s.xi := by
      simp only [Matrix.sub_mul]
      abel
    have hrev : hsNorm ((W-J)*s.xi)=hsNorm ((J-W)*s.xi) := by
      rw [Matrix.sub_mul,CountProof.hs_sub_rev,←Matrix.sub_mul]
    rw [heq,hrev] at ht
    have hvW : delta≤hs ((W-1)*s.xi) := by
      rw [MainProof.flatState_weighted_norm]
      exact hv
    simp only [hs_eq_hsNorm] at *
    linarith
  let p := (signProjection J true*s.rho).trace.re
  have hp : delta^2/16≤p := by
    have h := sector_probability s J hJ
    change hs ((J-1)*s.xi)^2=4*p at h
    nlinarith
  have hp0 : 0<p := (by positivity : (0:ℝ)<delta^2/16).trans_le hp
  let q := Real.sqrt p
  have hq : delta/4≤q := by
    have hsqQ : q^2=p := Real.sq_sqrt hp0.le
    have hq0 : 0≤q := Real.sqrt_nonneg p
    nlinarith
  have hq0 : 0<q := Real.sqrt_pos.mpr hp0
  obtain ⟨t,ht⟩ := sector_approximation s J hJ hp0
  have hbound (a : ℝ) (ha : a≤(K+2)*e) : a/q≤4*(K+2)*e/delta := by
    apply (div_le_div_iff₀ hq0 hdelt).mpr
    have h1 : a*delta≤((K+2)*e)*delta := mul_le_mul_of_nonneg_right ha hdelt.le
    have h2 := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ)≤4*(K+2)*e)
    nlinarith
  refine ⟨t,hr.1,?_,?_,?_⟩
  · intro r hmem
    have h := sector_weighted_bound s t J hJ hp0 ht (wordEval U r-1)
    rw [hflat J,mul_zero,add_zero] at h
    exact h.trans (hbound _ (by have hh := hrel r hmem; nlinarith))
  · intro j hj1 hj5
    have hpair : hs (comm (U j) W*s.xi)≤K*e := by
      have h := hcentral d U e he.le hr j hj1 hj5
      have hcentW : hs ((U j*W*(U j).conjTranspose*W.conjTranspose-1)*s.xi)≤K*e := by
        rw [MainProof.flatState_weighted_norm]
        rw [eval_comm_word U hr.1] at h
        simpa [wordEval,W] using h
      have hh := commutator_from_relator (U j) W s.xi (hr.1 j) hW
      rw [hflat (U j),hflat W] at hh
      linarith
    have hround := rounded_pair_bound (U j) W s.xi (hr.1 j) hW
    rw [hflat (U j)] at hround
    have hpairJ : hs (comm (U j) J*s.xi)≤(K+2)*e := by linarith
    have h := sector_commutator_bound s t (U j) J (hr.1 j) hJ hp0 ht
    rw [hflat (U j),hflat J,mul_zero,add_zero,add_zero] at h
    exact h.trans (hbound _ hpairJ)
  · have h := sector_marker_bound hd s t W J hW hJ hp0 ht
    rw [hflat J,mul_zero,add_zero] at h
    have hdif : hs ((W-J)*s.xi)≤e := by
      rw [Matrix.sub_mul,hs_eq_hsNorm,CountProof.hs_sub_rev,←Matrix.sub_mul,←hs_eq_hsNorm]
      exact hdiff
    exact h.trans (hbound _ (by nlinarith))

end
end Blueprint.SV

#print axioms Blueprint.SV.flat_visible_sector
