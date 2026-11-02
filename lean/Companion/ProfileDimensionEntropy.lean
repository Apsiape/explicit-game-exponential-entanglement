import Companion.ProfileBridges

namespace Companion.Analytic.ProfileProof
noncomputable section
open scoped BigOperators ENNReal
set_option maxHeartbeats 600000

theorem dimension_lower (g : LCS) (eps : ℝ) (he : 0≤eps) :
    stateDimensionProfile g (gameConstant g*Real.sqrt eps)≤gameDimensionProfile g eps := by
  rw [← precision_eq]
  unfold gameDimensionProfile
  apply le_sInf
  rintro v ⟨d,s,hw,rfl⟩
  obtain ⟨r,m,_,hr,_,_,_,_,_,V,hV,hrec⟩ := TransferProof.transfer g d d s eps he hw
  calc
    _≤(r:ℝ≥0∞) := by unfold stateDimensionProfile; exact sInf_le ⟨r,⟨m⟩,rfl⟩
    _≤(d:ℝ≥0∞) := by exact_mod_cast hr

theorem dimension_upper (g : LCS) (eps : ℝ) (he : 0≤eps) :
    gameDimensionProfile g eps≤stateDimensionProfile g (Real.sqrt (eps/returnConstant g.arity)) := by
  unfold stateDimensionProfile
  apply le_sInf
  rintro v ⟨d,⟨m⟩,rfl⟩
  have hw := returned_win m (Real.sqrt_nonneg _)
  rw [return_precision_loss g eps he] at hw
  exact sInf_le ⟨d,ReturnProof.returnMeasurementStrategy m,hw,rfl⟩

theorem entropy_lower (g : LCS) (eps : ℝ) (he : 0≤eps) :
    stateEntropyProfile g (gameConstant g*Real.sqrt eps)≤gameEntropyProfile g eps := by
  rw [← precision_eq]
  unfold gameEntropyProfile
  apply le_sInf
  rintro v ⟨d,s,hw,rfl⟩
  obtain ⟨r,m,_,hr,_,_,_,_,_,V,hV,hrec⟩ := TransferProof.transfer g d d s eps he hw
  calc
    _≤ENNReal.ofReal (entropy m.state.rho) := by unfold stateEntropyProfile; exact sInf_le ⟨r,m,rfl⟩
    _=ENNReal.ofReal (entropy (s.psi*s.psi.conjTranspose)) :=
      congrArg ENNReal.ofReal (transfer_entropy s m.state V hV hrec).symm

theorem entropy_upper (g : LCS) (eps : ℝ) (he : 0≤eps) :
    gameEntropyProfile g eps≤stateEntropyProfile g (Real.sqrt (eps/returnConstant g.arity)) := by
  unfold stateEntropyProfile
  apply le_sInf
  rintro v ⟨d,m,rfl⟩
  have hw := returned_win m (Real.sqrt_nonneg _)
  rw [return_precision_loss g eps he] at hw
  apply sInf_le
  refine ⟨d,ReturnProof.returnMeasurementStrategy m,hw,?_⟩
  rw [returned_reduced]

end
end Companion.Analytic.ProfileProof
