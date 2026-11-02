import Companion.EntropyRank

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

/-- The unchanged uniform entropy/rank corollary of Theorem C. -/
theorem uniformCount : UniformCount := by
  intro M d X Z s k hM hX hZ hZZ hXZ ha hcX hcZ hsmall
  have hA (i : Fin M) :
      (Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2≤16*(M:ℝ)*k^2 := by
    have h0 : 0≤aSquared Z s i := by
      rw [← countEmbedding_shift_error Z hZ s i]
      exact sq_nonneg _
    exact uniform_augmented_error M hM _ _ k h0 (uniform_aSquared X Z s k hZ hZZ hcZ i)
      (hsNorm_nonneg _) (hcZ i)
  have hB (i : Fin M) :
      (Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2≤16*(M:ℝ)*k^2 := by
    have h0 : 0≤bSquared X Z s i := by
      rw [← countEmbedding_twist_error X Z hZ s i]
      exact sq_nonneg _
    exact uniform_augmented_error M hM _ _ k h0 (uniform_bSquared X Z s k hX hZ hXZ ha hcZ i)
      (hsNorm_nonneg _) (hcX i)
  have hbracket (i : Fin M) : (3/4:ℝ)≤
      1-(Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2/(2*Real.log 2)-
        binaryEntropy (min ((Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4) (1/2)) :=
    uniform_count_bracket _ _ (sq_nonneg _) ((hA i).trans hsmall) ((hB i).trans hsmall)
  have he : (3/4:ℝ)*M≤entropy s.rho := by
    calc
      _=∑ _i : Fin M, (3/4:ℝ) := by simp [mul_comm]
      _≤∑ i, (1-(Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2/(2*Real.log 2)-
          binaryEntropy (min ((Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4) (1/2))) :=
        Finset.sum_le_sum (fun i _ => hbracket i)
      _≤entropy s.rho := count_entropy_bound X Z hX hZ s
  exact ⟨he,entropy_rank_lower s _ he⟩

end
end Companion.Analytic.CountProof
