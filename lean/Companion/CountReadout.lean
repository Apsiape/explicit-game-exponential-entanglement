import Companion.JointCovariance

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

theorem countEmbedding_state_twist_bound {M d : Nat} (X Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) (i : Fin M) :
    hsNorm ((countEmbedding Z hZ*s.xi)*X i-cubeTwist (X i) i*(countEmbedding Z hZ*s.xi))≤
      Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi) := by
  let W := countEmbedding Z hZ
  let D := cubeTwist (X i) i
  have he : (W*s.xi)*X i-D*(W*s.xi)=
      W*(s.xi*X i-X i*s.xi)+(W*X i-D*W)*s.xi := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have ha : hsNorm ((W*X i-D*W)*s.xi)=Real.sqrt (bSquared X Z s i) := by
    have h := countEmbedding_twist_error X Z hZ s i
    have hn : hsNorm ((W*X i-D*W)*s.xi)=hsNorm ((D*W-W*X i)*s.xi) := by
      rw [← neg_sub (D*W) (W*X i),Matrix.neg_mul]
      simp only [hsNorm_eq_frobenius,norm_neg]
    rw [hn]
    rw [← h,Real.sqrt_sq (hsNorm_nonneg _)]
  have hc : hsNorm (W*(s.xi*X i-X i*s.xi))=hs (comm (X i) s.xi) := by
    rw [hsNorm_isometry_left _ _ (countEmbedding_isometry Z hZ),hs_eq_hsNorm]
    exact hs_sub_rev _ _
  rw [he]
  exact (hsNorm_add_le _ _).trans_eq (by rw [hc,ha,add_comm])

theorem count_factor_twist_distance {M d : Nat} (X Z : Fin M → Mat d)
    (hX : ∀ i, IsInvolution (X i)) (hZ : ∀ i, IsInvolution (Z i)) (s : State d) (i : Fin M) :
    hsNorm ((countEmbedding Z hZ*s.xi)-cubeTwist (X i) i*(countEmbedding Z hZ*s.xi)*X i)≤
      Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi) := by
  let K := countEmbedding Z hZ*s.xi
  have he : (K-cubeTwist (X i) i*K*X i)*X i=K*X i-cubeTwist (X i) i*K := by
    rw [Matrix.sub_mul,Matrix.mul_assoc _ (X i) (X i),(hX i).2,Matrix.mul_one]
  rw [← hsNorm_unitary_right (X i) (K-cubeTwist (X i) i*K*X i) (involution_unitary _ (hX i)).2,he]
  exact countEmbedding_state_twist_bound X Z hZ s i

/-- The complete lower entropy estimate of Step 4 for the actual joint
cube-shift pinching and the actual Pauli twists. -/
theorem count_pinching_entropy_lower {M d : Nat} (X Z : Fin M → Mat d)
    (hX : ∀ i, IsInvolution (X i)) (hZ : ∀ i, IsInvolution (Z i)) (s : State d) :
    (∑ i, (1-(Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2/(2*Real.log 2)))≤
      ((channelRun M (fun i => pinchingChannel (cubeShift (d:=d) i)
        (cubeShift_involution i))).applyState (embeddedCountState Z hZ s)).vonNeumann := by
  let C := fun i : Fin M => cubeShift (d:=d) i
  let P := jointProjection M C
  let K := countEmbedding Z hZ*s.xi
  have hK : hsNorm K=1 := countEmbedding_state_norm Z hZ s
  have hP : ∑ g, (P g).conjTranspose*P g=1 := jointProjection_complete M C cubeShift_involution
  have hh : ∀ g, (P g).conjTranspose=P g :=
    jointProjection_hermitian M C (fun i => (cubeShift_involution i).1) cubeShift_commute
  have hm : ∀ g h, P g*P h=if g=h then P g else 0 :=
    jointProjection_mul M C cubeShift_involution cubeShift_commute
  have hf (i : Fin M) (g : Fin M → Bool) :
      hsNorm (P g*(cubeTwist (X i) i*K*X i))=hsNorm (P (flip g i)*K) := by
    have hD : (cubeTwist (X i) i).conjTranspose*cubeTwist (X i) i=1 := by
      rw [(cubeTwist_involution _ (hX i) i).1,(cubeTwist_involution _ (hX i) i).2]
    exact jointProjection_flipped_norm M C _ hD i (cubeTwist_anticommute (X i) i)
      (fun j hj => cubeTwist_commute (X i) i j (Ne.symm hj)) K (involutionUnitary (X i) (hX i)) g
  have hl := readout_entropy_bound P hP K hK (fun i => cubeTwist (X i) i*K*X i) hf
    (fun i => Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))
    (fun i => add_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg _))
    (fun i => count_factor_twist_distance X Z hX hZ s i)
  apply hl.trans
  apply orthogonal_factor_entropy_lower P hh hm hP K hK
  have he := countEmbedding_factorState Z hZ s
  have heM := congrArg QIT.State.matrix he
  change K*K.conjTranspose=(embeddedCountState Z hZ s).matrix at heM
  change (channelRun M (fun i => pinchingChannel (C i) (cubeShift_involution i))).map
    (embeddedCountState Z hZ s).matrix=_
  rw [channelRun_jointProjection,← heM]
  change (∑ g, P g*(K*K.conjTranspose)*(P g).conjTranspose)=_
  simp_rw [hh]

end
end Companion.Analytic.CountProof
