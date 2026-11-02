import Blueprint.AWordArea
import Blueprint.ASector
import Blueprint.AHash
import Blueprint.AConstants
import Blueprint.MixedStates
import Blueprint.SpatialDefinitions
import Blueprint.A.SpatialExclusion

namespace Blueprint.AMain
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ENNReal
set_option maxHeartbeats 600000

theorem pure_lower
    (hconj : Published.ConjugatorLengths) : MainPureLower := by
  intro a b s eps he hsmall hw
  obtain ⟨d,rho,U,hm,hv,hent⟩ := AWordArea.strategy_pullback a b s eps he hsmall hw
  obtain ⟨hp,hscale,hconstant⟩ := AConstants.lower_constants eps he hsmall
  have hsc : cStar*Real.sqrt eps≤(2:ℝ)^(-1071:ℤ)*(1/2) := by
    convert hscale using 1 <;> norm_num
    rw [show (2:ℝ)^1072=(2:ℝ)^1071*2 from pow_succ _ _]
    field_simp
  have hs := ASector.source_sector hconj U rho _ (1/2) hp (by norm_num) (by norm_num) hm hv hsc
  have hs' : sourceC/256/(cStar*Real.sqrt eps)^2*bfun (cStar*Real.sqrt eps)-1≤entropy rho.rho := by
    convert hs.1 using 1 <;> ring
  refine ⟨?_,?_⟩
  · rw [← hent]
    exact hconstant.trans hs'
  · exact CountProof.entropy_le_log_rank (State.ofQuAIR (CountProof.factorState s.psi s.normalized))

theorem value_one (hhash : Published.PauliHashModels) : quantumValueOne MainProof.concreteLCS := by
  intro eps he
  obtain ⟨d,s,_,hw,_⟩ := AHash.small_error_strategy hhash (min eps (1/2)) (lt_min he (by norm_num)) (min_le_right _ _)
  exact ⟨d,s,(by linarith [min_le_left eps (1/2)] : 1-eps≤1-min eps (1/2)).trans hw⟩

theorem dimension_from_log (d : Nat) (K : ℝ) (hK : 0≤K) (h : log2 d≤K) :
    (d:ℝ)≤Real.exp K := by
  by_cases hd : d=0
  · subst d
    exact_mod_cast (Real.exp_pos K).le
  have hp : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
  apply (Real.log_le_iff_le_exp hp).mp
  have hl := (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp h
  have htwo : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  exact hl.trans (by nlinarith)

theorem upper (hhash : Published.PauliHashModels) : MainUpper := by
  intro eps he hsmall
  obtain ⟨d,s,hflat,hw,hlog⟩ := AHash.small_error_strategy hhash eps he hsmall
  have hK : 0≤mainUpperC/eps*log2 (1/eps) := by
    apply mul_nonneg
    · exact div_nonneg (by norm_num [mainUpperC]) he.le
    · exact div_nonneg (Real.log_nonneg (by have := he.le; rw [le_div_iff₀ he]; linarith)) (Real.log_pos (by norm_num)).le
  have hd := dimension_from_log d _ hK hlog
  calc
    _≤(d:ℝ≥0∞) := by unfold maximalEntanglementProfile; exact sInf_le ⟨d,s,hflat,hw,rfl⟩
    _≤_ := by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hd

theorem finite_exclusion (h : MainPureLower) :
    ∀ a b (s : Strategy MainProof.concreteLCS a b), win s≠1 := by
  intro a b s hw
  have hbig : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0),
      entropy (s.psi*s.psi.conjTranspose)+1≤mainRate e :=
    AConstants.main_rate_diverges.eventually (Filter.eventually_ge_atTop _)
  have hsmall : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), e<mainEps := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact eventually_lt_nhds (by unfold mainEps; positivity : (0:ℝ)<mainEps)
  have hpos : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), 0<e := self_mem_nhdsWithin
  obtain ⟨e,hb,hs,he⟩ := (hbig.and (hsmall.and hpos)).exists
  have hl := (h a b s e he hs.le (by rw [hw]; linarith)).1
  linarith

/-- The projective literature clause is explicit; the POVM, score and answer
conventions are converted by the proved spatial bridge. -/
theorem spatial_exclusion (hlit : Published.TensorPerfectFinite) (g : LCS)
    (h : ∀ a b (s : Strategy g a b), win s≠1) : NoSpatialPerfect g :=
  SpatialProof.spatial_exclusion_proof hlit g h

theorem strategy_profile_lower (hl : MainPureLower) (eps : ℝ) (he : 0<eps) (heps : eps≤mainEps)
    (family : ∀ d, Strategy MainProof.concreteLCS d d → Prop)
    (hex : ∃ d, ∃ s : Strategy MainProof.concreteLCS d d, family d s ∧ 1-eps≤win s) :
    mainRate eps≤log2 ((sInf {v : ℝ≥0∞ | ∃ d, ∃ s : Strategy MainProof.concreteLCS d d,
      family d s ∧ 1-eps≤win s ∧ v=(d:ℝ≥0∞)}).toReal) := by
  classical
  let d := Nat.find hex
  obtain ⟨s,hfam,hw⟩ := Nat.find_spec hex
  have hInf : sInf {v : ℝ≥0∞ | ∃ d, ∃ s : Strategy MainProof.concreteLCS d d,
      family d s ∧ 1-eps≤win s ∧ v=(d:ℝ≥0∞)}=(d:ℝ≥0∞) := by
    apply le_antisymm
    · exact sInf_le ⟨d,s,hfam,hw,rfl⟩
    · apply le_sInf
      rintro v ⟨k,t,ht,hwin,rfl⟩
      exact_mod_cast Nat.find_min' hex ⟨t,ht,hwin⟩
  rw [hInf,ENNReal.toReal_natCast]
  exact (hl d d s eps he heps hw).1.trans
    (entropy_le_log_dimension (State.ofQuAIR (CountProof.factorState s.psi s.normalized)))

theorem game_le_maximal (eps : ℝ) :
    gameDimensionProfile MainProof.concreteLCS eps≤maximalEntanglementProfile MainProof.concreteLCS eps := by
  unfold maximalEntanglementProfile
  apply le_sInf
  rintro v ⟨d,s,_,hw,rfl⟩
  exact sInf_le ⟨d,s,hw,rfl⟩

theorem maximal_feasible (hu : MainUpper) (eps : ℝ) (he : 0<eps) (heps : eps≤1/2) :
    ∃ d, ∃ s : Strategy MainProof.concreteLCS d d,
      s.psi=(((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • (1:Mat d) ∧ 1-eps≤win s := by
  classical
  by_contra hx
  have hz : maximalEntanglementProfile MainProof.concreteLCS eps=∞ := by
    apply le_antisymm le_top
    unfold maximalEntanglementProfile
    apply le_sInf
    rintro v ⟨d,s,hflat,hw,_⟩
    exact False.elim (hx ⟨d,s,hflat,hw⟩)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hu eps he heps) hz

theorem mainEps_le_half : mainEps≤1/2 := by
  have hh : mainEps≤(2:ℝ)^(-1:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-5500:ℤ)≤-1)
  simpa using hh

theorem asymptotics (hl : MainPureLower) (hu : MainUpper) :
    profileExponent (gameDimensionProfile MainProof.concreteLCS) ∧
      profileExponent (maximalEntanglementProfile MainProof.concreteLCS) := by
  have hgameUpper : ∀ eps : ℝ, 0<eps → eps≤1/2 →
      gameDimensionProfile MainProof.concreteLCS eps≤
        ENNReal.ofReal (Real.exp (mainUpperC/eps*log2 (1/eps))) := by
    intro eps he heps
    exact (game_le_maximal eps).trans (hu eps he heps)
  have hgameLower : ∀ eps : ℝ, 0<eps → eps≤mainEps →
      mainRate eps≤log2 ((gameDimensionProfile MainProof.concreteLCS eps).toReal) := by
    intro eps he heps
    have hex : ∃ d, ∃ s : Strategy MainProof.concreteLCS d d, True ∧ 1-eps≤win s := by
      obtain ⟨d,s,_,hw⟩ := maximal_feasible hu eps he (heps.trans mainEps_le_half)
      exact ⟨d,s,True.intro,hw⟩
    simpa only [gameDimensionProfile,true_and] using strategy_profile_lower hl eps he heps (fun _ _ => True) hex
  have hmaxLower : ∀ eps : ℝ, 0<eps → eps≤mainEps →
      mainRate eps≤log2 ((maximalEntanglementProfile MainProof.concreteLCS eps).toReal) := by
    intro eps he heps
    have heHalf : eps≤1/2 := heps.trans mainEps_le_half
    obtain ⟨d,s,hflat,hw⟩ := maximal_feasible hu eps he heHalf
    exact strategy_profile_lower hl eps he heps
      (fun d s => s.psi=(((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • (1:Mat d)) ⟨d,s,hflat,hw⟩
  refine ⟨AConstants.profile_squeeze _ hgameLower hgameUpper ?_,AConstants.profile_squeeze _ hmaxLower hu ?_⟩
  · intro eps he heps
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgameUpper eps he heps)
  · intro eps he heps
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hu eps he heps)

end
end Blueprint.AMain

-- ROUND-12 DECLARATION AUDIT
#print axioms Blueprint.AMain.pure_lower
#print axioms Blueprint.AMain.value_one
#print axioms Blueprint.AMain.dimension_from_log
#print axioms Blueprint.AMain.upper
#print axioms Blueprint.AMain.finite_exclusion
#print axioms Blueprint.AMain.spatial_exclusion
#print axioms Blueprint.AMain.strategy_profile_lower
#print axioms Blueprint.AMain.game_le_maximal
#print axioms Blueprint.AMain.maximal_feasible
#print axioms Blueprint.AMain.mainEps_le_half
#print axioms Blueprint.AMain.asymptotics
