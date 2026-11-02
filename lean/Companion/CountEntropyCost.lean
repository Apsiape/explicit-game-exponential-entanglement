import Companion.CommutingPinching
import Companion.CountPairwise

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

theorem countEmbedding_factorState {M d : Nat} (Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) :
    factorState (countEmbedding Z hZ*s.xi) (countEmbedding_state_norm Z hZ s)=
      embeddedCountState Z hZ s := by
  apply QIT.State.ext
  change (countEmbedding Z hZ*s.xi)*(countEmbedding Z hZ*s.xi).conjTranspose=
    countEmbedding Z hZ*s.rho*(countEmbedding Z hZ).conjTranspose
  rw [Matrix.conjTranspose_mul,s.xi_positive.isHermitian.eq]
  calc
    _=countEmbedding Z hZ*(s.xi*s.xi)*(countEmbedding Z hZ).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [s.xi_square]

/-- The state-dependent intertwining bound, with the commutator term
appearing exactly once, for the actual coherent embedding. -/
theorem countEmbedding_state_shift_bound {M d : Nat} (Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) (i : Fin M) :
    hsNorm ((countEmbedding Z hZ*s.xi)*Z i-cubeShift i*(countEmbedding Z hZ*s.xi))≤
      Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi) := by
  let W := countEmbedding Z hZ
  have he : (W*s.xi)*Z i-cubeShift i*(W*s.xi)=
      W*(s.xi*Z i-Z i*s.xi)+(W*Z i-cubeShift i*W)*s.xi := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have ha : hsNorm ((W*Z i-cubeShift i*W)*s.xi)=Real.sqrt (aSquared Z s i) := by
    have h := countEmbedding_shift_error Z hZ s i
    have hn : hsNorm ((W*Z i-cubeShift i*W)*s.xi)=
        hsNorm ((cubeShift i*W-W*Z i)*s.xi) := by
      rw [← neg_sub (cubeShift i*W) (W*Z i),Matrix.neg_mul]
      simp only [hsNorm_eq_frobenius,norm_neg]
    rw [hn]
    rw [← h,Real.sqrt_sq (hsNorm_nonneg _)]
  have hc : hsNorm (W*(s.xi*Z i-Z i*s.xi))=hs (comm (Z i) s.xi) := by
    rw [hsNorm_isometry_left _ _ (countEmbedding_isometry Z hZ),hs_eq_hsNorm]
    exact hs_sub_rev _ _
  rw [he]
  calc
    _≤hsNorm (W*(s.xi*Z i-Z i*s.xi))+hsNorm ((W*Z i-cubeShift i*W)*s.xi) := by
      simpa only [hsNorm_eq_frobenius] using norm_add_le
        (W*(s.xi*Z i-Z i*s.xi)) ((W*Z i-cubeShift i*W)*s.xi)
    _=_ := by rw [hc,ha,add_comm]

/-- The complete upper entropy estimate of Step 5 of the count proof.
All channels are the actual commuting cube-shift pinchings. -/
theorem count_pinching_entropy_cost {M d : Nat} (Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) :
    ((channelRun M (fun i => pinchingChannel (cubeShift (d:=d) i)
      (cubeShift_involution i))).applyState (embeddedCountState Z hZ s)).vonNeumann≤
        entropy s.rho+∑ i, binaryEntropy
          (min ((Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4) (1/2)) := by
  have h := commuting_pinching_factor_bound M (fun i => cubeShift (d:=d) i)
    cubeShift_involution cubeShift_commute (countEmbedding Z hZ*s.xi)
    (countEmbedding_state_norm Z hZ s) (fun i => involutionUnitary (Z i) (hZ i))
    (fun i => Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))
    (fun i => add_nonneg (Real.sqrt_nonneg _) (by rw [hs_eq_hsNorm]; exact hsNorm_nonneg _))
    (fun i => countEmbedding_state_shift_bound Z hZ s i)
  rw [countEmbedding_factorState,countEmbedding_entropy] at h
  exact h

end
end Companion.Analytic.CountProof
