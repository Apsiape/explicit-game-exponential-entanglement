import Blueprint.FProfile
import Blueprint.ASector
import Blueprint.SV.NumericModels
import Blueprint.SV.NumericAreas
import Blueprint.SV.ModelPullback

namespace Blueprint.FSVGame
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def SVSpecification (g : LCS) : Prop :=
  (∀ i j, g.pi i j=1/((g.system.equations.length:ℝ)*g.system.n)) ∧
  quantumValueOne g ∧
  (∃ images : Nat → Word, ∃ z : Word,
    (∀ r∈kRelators, ∃ k, HasArea g.system (substituteWords images r) k) ∧
    (∀ j, 1≤j → j≤5 → ∃ k, HasArea g.system
      (substituteWords images (ASector.commWord [(j,true)] [(3,true)])) k) ∧
    ∃ k, HasArea g.system (ASector.commWord (images 3) z++[neg g.system.n]) k) ∧
  (∃ C : ℝ, 0<C ∧ ∀ e, 0<e → e≤1 → gameDimensionProfile g e≤ENNReal.ofReal (C/Real.sqrt e))

/-- Explicit uniform-question game from the balanced lift of paper Lemma 11.13,
including the finite-area pullback data and the inverse-square-root upper rate. -/
theorem construction : ∃ g : LCS, SVSpecification g := by
  refine ⟨SV.numericGame,SV.numericGame_distribution,SV.numeric_game_upper.1,
    SV.numeric_area_data,SV.numeric_game_upper.2⟩
def game : LCS := Classical.choose construction
theorem specification : SVSpecification game := Classical.choose_spec construction

theorem sector_pullback : ∃ C : ℝ, 0<C ∧ ∀ d (s : Strategy game d d) e,
    0<e → e≤1 → 1-e≤win s →
    (Real.sqrt e≤1/(5*C) → ∃ (r : Nat) (rho : State r) (U : Nat → Mat r),
      r≤d ∧ kModel U rho (60*C*Real.sqrt e)) := by
  obtain ⟨images,z,hrel,hcent,hmarker⟩ := specification.2.2.1
  obtain ⟨A,hA,hpull⟩ := SV.area_model_pullback game images z hrel hcent hmarker
  let C := A*gameConstant game
  have hC : 0<C := mul_pos (by linarith) (ProfileProof.gameConstant_pos game)
  refine ⟨C,hC,?_⟩
  intro d s e he _ hw hsmall
  obtain ⟨r,m,hr,hrd,_,_,hJ,_⟩ := TransferProof.transfer game d d s e he.le hw
  let b := C*Real.sqrt e
  have hb : 0≤b := mul_nonneg hC.le (Real.sqrt_nonneg e)
  have hcut : b≤1/5 := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ)<5*C)).mp hsmall
    dsimp [b]
    nlinarith
  have hscale : A*transferPrecision game e=b := by
    rw [ProfileProof.precision_eq]
    dsimp [b,C]
    ring
  obtain ⟨V,hV,hVr,hVc,hVcent,hvis⟩ := hpull r (transferPrecision game e) m
    (TransferProof.transferPrecision_nonneg game e) hJ
  rw [hscale] at hVr hVc hVcent hvis
  obtain ⟨t,ht⟩ := SV.negative_sector_model hr V m.state b hb hcut hV hVr hVc hVcent hvis
  refine ⟨r,t,V,hrd,?_⟩
  convert ht using 1
  dsimp [b]
  ring

theorem lower : ∃ c : ℝ, 0<c ∧ ∀ e, 0<e → e≤1 →
    ENNReal.ofReal (c/Real.sqrt e)≤gameDimensionProfile game e := by
  obtain ⟨C,hC,hsector⟩ := sector_pullback
  refine ⟨1/(1740*C),by positivity,?_⟩
  intro e he hsmall
  have hs : 0<Real.sqrt e := Real.sqrt_pos.mpr he
  unfold gameDimensionProfile
  apply le_sInf
  rintro v ⟨d,s,hw,rfl⟩
  have hd : 0<d := by
    by_contra hn
    have hd0 : d=0 := by omega
    subst d
    have hnorm := s.normalized
    simp [Companion.Analytic.hs] at hnorm
  have hlower : (1/(1740*C))/Real.sqrt e≤(d:ℝ) := by
    by_cases hcut : Real.sqrt e≤1/(5*C)
    · obtain ⟨r,rho,U,hr,hm⟩ := hsector d s e he hsmall hw hcut
      have hdim := FProfile.state_dimension U rho (60*C*Real.sqrt e) (by positivity) hm
      have hid : (1/(1740*C))/Real.sqrt e=1/(29*(60*C*Real.sqrt e)) := by ring
      rw [hid]
      exact hdim.trans (by exact_mod_cast hr)
    · have hcut' : 1/(5*C)<Real.sqrt e := lt_of_not_ge hcut
      have hcsmall : 1/(1740*C)≤1/(5*C) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      have hunit : (1/(1740*C))/Real.sqrt e≤1 :=
        (div_le_one hs).mpr (hcsmall.trans hcut'.le)
      exact hunit.trans (by exact_mod_cast hd)
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hlower

def GameRate : Prop := ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ e, 0<e → e≤1 →
  ENNReal.ofReal (c/Real.sqrt e)≤gameDimensionProfile game e ∧
  gameDimensionProfile game e≤ENNReal.ofReal (C/Real.sqrt e)

theorem upper : ∃ C : ℝ, 0<C ∧ ∀ e, 0<e → e≤1 →
    gameDimensionProfile game e≤ENNReal.ofReal (C/Real.sqrt e) := specification.2.2.2

def LogRate : Prop := ∃ C : ℝ, 0≤C ∧ ∀ e, 0<e → e≤1 →
  |log2 ((gameDimensionProfile game e).toReal)-(1/2)*log2 (1/e)|≤C

theorem log2_div_sqrt (c e : ℝ) (hc : 0<c) (he : 0<e) :
    log2 (c/Real.sqrt e)=log2 c+(1/2)*log2 (1/e) := by
  unfold log2
  rw [Real.log_div (ne_of_gt hc) (ne_of_gt (Real.sqrt_pos.mpr he)),
    Real.log_sqrt he.le,Real.log_div one_ne_zero (ne_of_gt he),Real.log_one]
  ring

theorem logarithmic (h : GameRate) : LogRate := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := h
  let K := max |log2 c| |log2 C|
  refine ⟨K,(abs_nonneg (log2 c)).trans (le_max_left _ _),?_⟩
  intro e he hsmall
  obtain ⟨hlo,hup⟩ := hbounds e he hsmall
  have hs : 0<Real.sqrt e := Real.sqrt_pos.mpr he
  have hfin : gameDimensionProfile game e≠⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  have hlR : c/Real.sqrt e≤(gameDimensionProfile game e).toReal := by
    simpa only [ENNReal.toReal_ofReal (div_nonneg hc.le hs.le)] using
      ENNReal.toReal_mono hfin hlo
  have huR : (gameDimensionProfile game e).toReal≤C/Real.sqrt e := by
    simpa only [ENNReal.toReal_ofReal (div_nonneg hC.le hs.le)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hup
  have hpos : 0<(gameDimensionProfile game e).toReal := (div_pos hc hs).trans_le hlR
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl := div_le_div_of_nonneg_right (Real.log_le_log (div_pos hc hs) hlR) hlog.le
  have hu := div_le_div_of_nonneg_right (Real.log_le_log hpos huR) hlog.le
  change log2 (c/Real.sqrt e)≤log2 ((gameDimensionProfile game e).toReal) at hl
  change log2 ((gameDimensionProfile game e).toReal)≤log2 (C/Real.sqrt e) at hu
  rw [log2_div_sqrt c e hc he] at hl
  rw [log2_div_sqrt C e hC he] at hu
  have hcK : -K≤log2 c := (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
  have hCK : log2 C≤K := (le_abs_self _).trans (le_max_right _ _)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end Blueprint.FSVGame
