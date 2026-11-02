import Companion.CountReadout

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

/-- Theorem C(iii), with precisely the entropy, norm, and error terms of
the unchanged challenge statement. -/
theorem count_entropy_bound {M d : Nat} (X Z : Fin M → Mat d)
    (hX : ∀ i, IsInvolution (X i)) (hZ : ∀ i, IsInvolution (Z i)) (s : State d) :
    (∑ i, (1-(Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2/(2*Real.log 2)-
      binaryEntropy (min ((Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4) (1/2))))≤entropy s.rho := by
  have hl := count_pinching_entropy_lower X Z hX hZ s
  have hu := count_pinching_entropy_cost Z hZ s
  rw [Finset.sum_sub_distrib]
  linarith

/-- All three parts of the original finite-dimensional Count statement. -/
theorem count : Count := by
  intro M d X Z s hX hZ
  exact ⟨count_a_bound Z s hZ, count_b_bound X Z s hX hZ, count_entropy_bound X Z hX hZ s⟩

end
end Companion.Analytic.CountProof
