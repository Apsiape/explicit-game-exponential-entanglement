import Blueprint.A.Diagram.Conjugators
import Blueprint.AMain
import Blueprint.ERates
import Blueprint.FSVGame
import Blueprint.EAsymptotics
import Blueprint.A.HashModelsProof

namespace Blueprint
noncomputable section
open Companion Companion.Analytic
set_option maxHeartbeats 600000

def AStatement : Prop :=
  MainProof.concreteLCS.system.n=1993 ∧ MainProof.concreteLCS.system.equations.length=1687 ∧
  MainProof.concreteLCS.arity=3 ∧ quantumValueOne MainProof.concreteLCS ∧
  (∀ a b (s : Strategy MainProof.concreteLCS a b), win s≠1) ∧ NoSpatialPerfect MainProof.concreteLCS ∧
  MainPureLower ∧ MainMixedLower ∧ MainUpper ∧
  profileExponent (gameDimensionProfile MainProof.concreteLCS) ∧
  profileExponent (maximalEntanglementProfile MainProof.concreteLCS)

def EStatement : Prop := ELower ∧ EProfiles ∧ EMixed ∧
  EAsymptotics.ThetaRate chshEntropyProfile ∧ EAsymptotics.ThetaRate EAsymptotics.formationProfile
def FStatement : Prop := KProfile ∧ FSVGame.GameRate ∧ quantumValueOne FSVGame.game ∧ FSVGame.LogRate

/-- Theorem A. All author obligations are proved. The sole parameter is the
published Cleve–Liu–Slofstra tensor-strategy clause. -/
theorem theoremA
    (hspatial : Published.TensorPerfectFinite) : AStatement := by
  let hconj := DiagramProof.conjugatorLengths
  let hhash := Published.pauliHashModels
  let lower := AMain.pure_lower hconj
  obtain ⟨hn,hm⟩ := MainProof.concreteLCS_sizes
  obtain ⟨hasym1,hasym2⟩ := AMain.asymptotics lower (AMain.upper hhash)
  exact ⟨hn,hm,MainProof.concreteLCS_arity,AMain.value_one hhash,AMain.finite_exclusion lower,
    AMain.spatial_exclusion hspatial _ (AMain.finite_exclusion lower),lower,
    MixedStates.main_from_pure lower,AMain.upper hhash,hasym1,hasym2⟩

theorem theoremE : EStatement := by
  have hm := MixedStates.chsh_from_pure ERates.entropy_lower
  obtain ⟨hp,hf⟩ := EAsymptotics.theta ERates.profiles hm
  exact ⟨ERates.entropy_lower,ERates.profiles,hm,hp,hf⟩

theorem theoremF : FStatement := by
  obtain ⟨c,hc,hl⟩ := FSVGame.lower
  obtain ⟨C,hC,hu⟩ := FSVGame.upper
  have hg : FSVGame.GameRate := ⟨c,C,hc,hC,fun e he he1 => ⟨hl e he he1,hu e he he1⟩⟩
  exact ⟨FProfile.profiles,hg,FSVGame.specification.2.1,FSVGame.logarithmic hg⟩

end
end Blueprint
