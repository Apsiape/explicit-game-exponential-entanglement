import Companion.TransferModelBuilder

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

/-- The full original finite-dimensional transfer theorem, including all
measurement reductions, full Schmidt support, exact J=-I and constants. -/
theorem transfer : Transfer := by
  intro g dA dB s eps heps hwin
  obtain ⟨r,dC,t,V,B,P,hp,hAdim,hBdim,hpd,hV,hrec,hw,hB,hBob,hAlice⟩ := transfer_prepared_strategy s
  have htwin : 1-eps≤win t := hwin.trans hw
  let st : State r := State.ofQuAIR (CountProof.factorState t.psi t.normalized)
  let G := usedBob B
  have hGi : ∀ j, IsInvolution (G j) := usedBob_involution B hB
  obtain ⟨W,hW,hpolar⟩ := schmidt_polar_factor t.psi hpd
  have hnorm (T : Mat r) : hs (T*st.xi)=hsNorm (T*t.psi) := by
    change hsNorm (T*QIT.psdSqrt (t.psi*t.psi.conjTranspose))=hsNorm (T*t.psi)
    exact polar_weighted_norm t.psi _ W hW hpolar T
  have hscstrong (j : Fin g.system.n) : hs (comm (G j) st.xi)≤Real.sqrt 2*theta g eps := by
    change hsNorm (comm (usedBob B j) (QIT.psdSqrt (t.psi*t.psi.conjTranspose)))≤_
    exact prepared_state_commutator t B P eps hB hBob hAlice heps htwin hpd j
  have hmax : Real.sqrt 2≤max (g.arity:ℝ) 4 := by
    have h4 : Real.sqrt 2≤4 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
    exact h4.trans (le_max_right _ _)
  have hsc (j : Fin g.system.n) : hs (comm (G j) st.xi)≤transferPrecision g eps :=
    (hscstrong j).trans (mul_le_mul_of_nonneg_right hmax (theta_nonneg g eps))
  have hcomm (i : Fin g.system.equations.length) (j k : Fin g.system.n)
      (hj : j.val ∈ (g.system.equations[i.val]).vars) (hk : k.val ∈ (g.system.equations[i.val]).vars) :
      hs ((G j*G k*G j*G k-1)*st.xi)≤transferPrecision g eps := by
    rw [hnorm]
    exact prepared_commutator_relation t B P eps hB hBob hAlice heps htwin i j k hj hk
  have hrow (i : Fin g.system.equations.length) :
      hs ((boolPhase (g.system.equations[i.val]).rhs •
        ((g.system.equations[i.val]).vars.map (naturalBob G)).prod-1)*st.xi)≤transferPrecision g eps := by
    rw [hnorm]
    exact prepared_equation_relation t B P eps hB hBob hAlice heps htwin i
  let m := modelFromSolutionBounds g st G (transferPrecision g eps) (transferPrecision_nonneg g eps) hGi hsc hcomm hrow
  refine ⟨r,m,hp,hAdim,hBdim,?_,?_,?_,?_,V,hV,?_⟩
  · exact hpd
  · exact solutionAssignment_J G
  · intro j _ _
    exact solutionAssignment_involution G hGi j
  · intro j hj1 hjn
    change hs (comm (solutionAssignment G j) st.xi)≤Real.sqrt 2*theta g eps
    unfold solutionAssignment
    rw [dite_eq_left (show 1≤j ∧ j≤g.system.n from ⟨hj1,hjn⟩)]
    exact hscstrong _
  · exact hrec

end
end Companion.Analytic.TransferProof
