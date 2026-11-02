import Blueprint.Definitions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Blueprint.AConstants
noncomputable section
open Companion Companion.Analytic
open scoped ENNReal
set_option maxHeartbeats 600000

def logDefect (t : ℝ) : ℝ := t-4*(24+log2 t)^2

theorem logDefect_derivative (t : ℝ) (ht : 0<t) :
    HasDerivAt logDefect (1-8*(24+log2 t)/(t*Real.log 2)) t := by
  have hh := (hasDerivAt_id t).sub
    ((((hasDerivAt_const t (24:ℝ)).add ((Real.hasDerivAt_log ht.ne').div_const (Real.log 2))).pow 2).const_mul 4)
  convert hh using 1
  · rfl
  · dsimp [log2]
    field_simp
    ring

theorem log2_linear_bound (t : ℝ) (ht : 0<t) : log2 t≤7+t/64 := by
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h128 : Real.log 128=7*Real.log 2 := by
    convert Real.log_pow 2 7 using 1 <;> norm_num
  have hh := Real.log_le_sub_one_of_pos (div_pos ht (by norm_num : (0:ℝ)<128))
  rw [Real.log_div ht.ne' (by norm_num),h128] at hh
  apply (div_le_iff₀ hL).mpr
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hhalf)]

theorem logDefect_monotone : MonotoneOn logDefect (Set.Ici 5500) := by
  have hd (t : ℝ) (ht : 5500≤t) := logDefect_derivative t (by linarith)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (5500:ℝ))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  have ht' : (5500:ℝ)≤t := interior_subset ht
  have hp : 0<t := by linarith
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh := log2_linear_bound t hp
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (mul_pos hp hL)).mpr
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hhalf)]

theorem logDefect_lower (t : ℝ) (ht : 5500≤t) : (171:ℝ)≤logDefect t := by
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog : log2 (5500:ℝ)≤25/2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<5500^2) (by norm_num : (5500:ℝ)^2≤2^25)
    rw [Real.log_pow,Real.log_pow] at hh
    apply (div_le_iff₀ hL).mpr
    norm_num at hh
    linarith
  have hzero : 0≤log2 (5500:ℝ) := div_nonneg (Real.log_nonneg (by norm_num)) hL.le
  have hsq : (24+log2 (5500:ℝ))^2≤(73/2:ℝ)^2 :=
    (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have hbase : (171:ℝ)≤logDefect 5500 := by unfold logDefect; nlinarith
  exact hbase.trans (logDefect_monotone (by simp) ht ht)

theorem main_rate_ge_one (eps : ℝ) (he : 0<eps) (hs : eps≤mainEps) : 1≤mainRate eps := by
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0<mainC := by norm_num [mainC]
  have hb : 0<bfun eps := Real.rpow_pos_of_pos (by norm_num) _
  let t := log2 (1/eps)
  have hl := Real.log_le_log he hs
  change Real.log eps≤Real.log ((2:ℝ)^(-5500:ℤ)) at hl
  rw [Real.log_zpow] at hl
  have ht : (5500:ℝ)≤t := by
    dsimp [t,log2]
    rw [one_div,Real.log_inv]
    apply (le_div_iff₀ hL).mpr
    norm_num at hl
    linarith
  have hcLow : (-112:ℝ)*Real.log 2≤Real.log mainC := by
    have hm : (2:ℝ)^(-112:ℤ)≤mainC := by norm_num [mainC]
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^(-112:ℤ)) hm
    simpa only [Real.log_zpow,Int.cast_neg,Int.cast_ofNat] using hh
  have hlogeps : Real.log eps= -(Real.log 2)*t := by
    dsimp [t,log2]
    simp only [one_div,Real.log_inv]
    field_simp
  have hidentity : Real.log (mainRate eps)=Real.log mainC+Real.log 2*logDefect t := by
    rw [mainRate,Real.log_mul (div_ne_zero hc.ne' he.ne') hb.ne',Real.log_div hc.ne' he.ne']
    have hB : Real.log (bfun eps)=(-4*(24+log2 t)^2)*Real.log 2 := Real.log_rpow (by norm_num : (0:ℝ)<2) _
    rw [hB,hlogeps]
    dsimp [logDefect]
    ring
  apply (Real.log_nonneg_iff (mul_pos (div_pos hc he) hb)).mp
  change 0≤Real.log (mainRate eps)
  rw [hidentity]
  have hh := mul_le_mul_of_nonneg_left (logDefect_lower t ht) hL.le
  nlinarith

theorem bfun_mono_small (a b : ℝ) (ha : 0<a) (hab : a≤b) (hb : b≤1/2) : bfun a≤bfun b := by
  have hb0 : 0<b := ha.trans_le hab
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have htB : 1≤log2 (1/b) := by
    have hdiv : (2:ℝ)≤1/b := (le_div_iff₀ hb0).mpr (by linarith)
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hdiv
    exact (le_div_iff₀ hL).mpr (by simpa using hh)
  have ht : log2 (1/b)≤log2 (1/a) := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact Real.log_le_log (div_pos (by norm_num) hb0) (one_div_le_one_div_of_le ha hab)
  have hlog : log2 (log2 (1/b))≤log2 (log2 (1/a)) :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) ht) hL.le
  have hnonneg : 0≤log2 (log2 (1/b)) := div_nonneg (Real.log_nonneg htB) hL.le
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
  have hsq := (sq_le_sq₀ (by linarith : (0:ℝ)≤24+log2 (log2 (1/b)))
    (by linarith : (0:ℝ)≤24+log2 (log2 (1/a)))).mpr (by linarith)
  nlinarith

theorem cstar_bounds : (1:ℝ)≤cStar ∧ cStar≤(2:ℝ)^40 := by
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤5061)
  have hp := Real.sqrt_nonneg (5061:ℝ)
  have hlo : 1≤Real.sqrt 5061 := by nlinarith
  have hhi : Real.sqrt 5061≤72 := by nlinarith
  constructor <;> norm_num [cStar,cPsi] <;> nlinarith

theorem cstar_precision_bound (eps : ℝ) (he : 0<eps) (hs : eps≤mainEps) :
    0<cStar*Real.sqrt eps ∧ cStar*Real.sqrt eps≤(2:ℝ)^(-1072:ℤ) ∧ eps≤cStar*Real.sqrt eps := by
  have hc : 0<cStar := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) cstar_bounds.1
  have heSmall : eps≤(2:ℝ)^(-2400:ℤ) := hs.trans
    (zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) (by norm_num : (-5500:ℤ)≤-2400))
  have hsq : ((2:ℝ)^(-1200:ℤ))^2=(2:ℝ)^(-2400:ℤ) := by
    rw [←zpow_natCast ((2:ℝ)^(-1200:ℤ)) 2,←zpow_mul]
    rfl
  have hsqrt : Real.sqrt eps≤(2:ℝ)^(-1200:ℤ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rwa [Real.sq_sqrt he.le,hsq]
  have hbound : cStar*Real.sqrt eps≤(2:ℝ)^(-1072:ℤ) := by
    calc
      _≤(2:ℝ)^40*(2:ℝ)^(-1200:ℤ) :=
        mul_le_mul cstar_bounds.2 hsqrt (Real.sqrt_nonneg _) (by positivity)
      _=(2:ℝ)^(-1160:ℤ) := by
        rw [←zpow_natCast (2:ℝ) 40,←zpow_add₀ (by norm_num : (2:ℝ)≠0)]
        rfl
      _≤_ := zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-1160:ℤ)≤-1072)
  have heOne : eps≤1 := hs.trans (by
    change (2:ℝ)^(-5500:ℤ)≤1
    simpa using zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) (by norm_num : (-5500:ℤ)≤0))
  have hsqrt' : eps≤Real.sqrt eps := by nlinarith [Real.sq_sqrt he.le,Real.sqrt_nonneg eps]
  exact ⟨mul_pos hc (Real.sqrt_pos.mpr he),hbound,
    hsqrt'.trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) cstar_bounds.1)⟩

theorem cstar_coefficient : 2*mainC*cStar^2≤sourceC/256 := by
  have hs : cStar^2=(294240:ℝ)^2*5061*cPsi^2 := by
    unfold cStar
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤5061)]
  rw [hs]
  norm_num [mainC,sourceC,cPsi]

theorem lower_constants (eps : ℝ) (he : 0<eps) (hs : eps≤mainEps) :
    0<cStar*Real.sqrt eps ∧ cStar*Real.sqrt eps≤(2:ℝ)^(-1072:ℤ) ∧
    mainRate eps≤sourceC/256/(cStar*Real.sqrt eps)^2*bfun (cStar*Real.sqrt eps)-1 := by
  obtain ⟨hp,hprec,heE⟩ := cstar_precision_bound eps he hs
  have hhalf : cStar*Real.sqrt eps≤1/2 := hprec.trans (by
    have hh := zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) (by norm_num : (-1072:ℤ)≤-1)
    simpa using hh)
  have hb := bfun_mono_small eps (cStar*Real.sqrt eps) he heE hhalf
  have hc : cStar≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) cstar_bounds.1)
  have hmul : 2*mainRate eps≤sourceC/256/(cStar*Real.sqrt eps)^2*bfun (cStar*Real.sqrt eps) := by
    calc
      _=(2*mainC*cStar^2)/(cStar*Real.sqrt eps)^2*bfun eps := by
        rw [mul_pow,Real.sq_sqrt he.le]
        unfold mainRate
        field_simp
      _≤_ := mul_le_mul (div_le_div_of_nonneg_right cstar_coefficient (sq_nonneg _)) hb
        (Real.rpow_pos_of_pos (by norm_num) _).le (by unfold sourceC; positivity)
  exact ⟨hp,hprec,by linarith [main_rate_ge_one eps he hs]⟩


theorem bfun_asymptotics :
    Filter.Tendsto (fun e => Real.log (bfun e)/Real.log e)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Filter.Tendsto (fun t : ℝ => Real.log t/t) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1:ℝ)≠0)
  have h2 : Filter.Tendsto (fun t : ℝ => (Real.log t)^2/t) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num : (1:ℝ)≠0)
  have h0 : Filter.Tendsto (fun t : ℝ => 1/t) Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hsum := ((h0.const_mul 2304).add (h1.const_mul (192/Real.log 2))).add
    (h2.const_mul (4/(Real.log 2)^2))
  have hpoly : Filter.Tendsto (fun t : ℝ => 4*(24+log2 t)^2/t) Filter.atTop (nhds 0) := by
    have hh : Filter.Tendsto (fun t : ℝ => 2304*(1/t)+(192/Real.log 2)*(Real.log t/t)+
        (4/(Real.log 2)^2)*((Real.log t)^2/t)) Filter.atTop (nhds 0) := by simpa using hsum
    apply hh.congr'
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
    dsimp [log2]
    field_simp
    ring
  have ht : Filter.Tendsto (fun e : ℝ => log2 (1/e)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have hi : Filter.Tendsto (fun e : ℝ => 1/e) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    exact (Real.tendsto_log_atTop.comp hi).atTop_div_const hL
  apply (hpoly.comp ht).congr'
  filter_upwards [ht.eventually (Filter.eventually_gt_atTop (0:ℝ))] with e he
  have heq : Real.log e= -(Real.log 2)*log2 (1/e) := by
    simp only [log2,one_div,Real.log_inv]
    field_simp
  dsimp [Function.comp_def]
  rw [show Real.log (bfun e)=(-4*(24+log2 (log2 (1/e)))^2)*Real.log 2 by
    exact Real.log_rpow (by norm_num : (0:ℝ)<2) _]
  conv_rhs => rw [heq]
  field_simp

theorem main_rate_diverges : Filter.Tendsto mainRate (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hc : 0<mainC := by norm_num [mainC]
  have hb (e : ℝ) : 0<bfun e := Real.rpow_pos_of_pos (by norm_num) _
  have hcoef : Filter.Tendsto (fun e : ℝ => 1-Real.log (bfun e)/Real.log e)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using (tendsto_const_nhds.sub bfun_asymptotics :
      Filter.Tendsto (fun e : ℝ => 1-Real.log (bfun e)/Real.log e)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1-0)))
  have hminus : Filter.Tendsto (fun e : ℝ => -Real.log e)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hprod := Filter.Tendsto.pos_mul_atTop (by norm_num : (0:ℝ)<1) hcoef hminus
  have hlog : Filter.Tendsto (fun e : ℝ => Real.log (mainRate e))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    apply (Filter.tendsto_atTop_add_const_left _ (Real.log mainC) hprod).congr'
    have hsmall : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), e<1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [self_mem_nhdsWithin,hsmall] with e he he1
    have hle : Real.log e≠0 := ne_of_lt (Real.log_neg he he1)
    rw [mainRate,Real.log_mul (div_ne_zero hc.ne' (ne_of_gt he)) (hb e).ne',
      Real.log_div hc.ne' (ne_of_gt he)]
    field_simp
    ring
  apply (Real.tendsto_exp_atTop.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  exact Real.exp_log (mul_pos (div_pos hc he) (hb e))

theorem main_rate_log_exponent : Filter.Tendsto (fun e : ℝ => Real.log (mainRate e)/Real.log (1/e))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hc : 0<mainC := by norm_num [mainC]
  have hb (e : ℝ) : 0<bfun e := Real.rpow_pos_of_pos (by norm_num) _
  have ht : Filter.Tendsto (fun e : ℝ => Real.log (1/e)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have hi : Filter.Tendsto (fun e : ℝ => 1/e) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    exact Real.tendsto_log_atTop.comp hi
  have hi := (tendsto_inv_atTop_zero.comp ht).const_mul (Real.log mainC)
  have hcoef : Filter.Tendsto (fun e : ℝ => 1-Real.log (bfun e)/Real.log e)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using (tendsto_const_nhds.sub bfun_asymptotics :
      Filter.Tendsto (fun e : ℝ => 1-Real.log (bfun e)/Real.log e)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1-0)))
  have hh := hi.add hcoef
  have hlim : Filter.Tendsto (fun e : ℝ => Real.log mainC*(Real.log (1/e))⁻¹+
      (1-Real.log (bfun e)/Real.log e)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [Function.comp_def,mul_zero,zero_add] using hh
  apply hlim.congr'
  have hsmall : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), e<1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [self_mem_nhdsWithin,hsmall] with e he he1
  have hne := ne_of_lt (Real.log_neg he he1)
  rw [mainRate,Real.log_mul (div_ne_zero hc.ne' he.ne') (hb e).ne',Real.log_div hc.ne' he.ne']
  simp only [one_div,Real.log_inv]
  field_simp
  ring

theorem profile_squeeze (f : ℝ → ℝ≥0∞)
    (hl : ∀ e, 0<e → e≤mainEps → mainRate e≤log2 ((f e).toReal))
    (hu : ∀ e, 0<e → e≤1/2 → f e≤ENNReal.ofReal (Real.exp (mainUpperC/e*log2 (1/e))))
    (hf : ∀ e, 0<e → e≤1/2 → f e≠∞) : profileExponent f := by
  let K := mainUpperC/(Real.log 2)^2
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0<K := div_pos (by norm_num [mainUpperC]) (sq_pos_of_pos hL)
  have ht : Filter.Tendsto (fun e : ℝ => Real.log (1/e)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have hi : Filter.Tendsto (fun e : ℝ => 1/e) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    exact Real.tendsto_log_atTop.comp hi
  have hlog : Filter.Tendsto (fun t : ℝ => Real.log t/t) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1:ℝ)≠0)
  have hzero : Filter.Tendsto (fun t : ℝ => 1/t) Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hupper : Filter.Tendsto (fun e : ℝ =>
      1+Real.log K*(1/Real.log (1/e))+Real.log (Real.log (1/e))/Real.log (1/e))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : ℝ => (1:ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have hh := ((hone.add (hzero.const_mul (Real.log K))).add hlog).comp ht
    simpa only [Function.comp_def,mul_zero,add_zero] using hh
  unfold profileExponent
  apply main_rate_log_exponent.squeeze' hupper
  · have hsmall : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), e<min mainEps (1/2) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (by unfold mainEps; positivity : (0:ℝ)<min mainEps (1/2)))
    filter_upwards [self_mem_nhdsWithin,hsmall] with e he heSmall
    have hlt : e<1 := lt_trans (lt_of_lt_of_le heSmall (min_le_right _ _)) (by norm_num)
    have hT : 0<Real.log (1/e) := by rw [one_div,Real.log_inv]; exact neg_pos.mpr (Real.log_neg he hlt)
    apply div_le_div_of_nonneg_right _ hT.le
    exact Real.log_le_log (mul_pos (div_pos (by norm_num [mainC]) he)
      (Real.rpow_pos_of_pos (by norm_num) _)) (hl e he ((lt_of_lt_of_le heSmall (min_le_left _ _)).le))
  · have hsmall : ∀ᶠ e in nhdsWithin (0:ℝ) (Set.Ioi 0), e<min mainEps (1/2) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (by unfold mainEps; positivity : (0:ℝ)<min mainEps (1/2)))
    filter_upwards [self_mem_nhdsWithin,hsmall] with e he heSmall
    have he1 : e≤1/2 := (lt_of_lt_of_le heSmall (min_le_right _ _)).le
    have heE : e≤mainEps := (lt_of_lt_of_le heSmall (min_le_left _ _)).le
    let t := Real.log (1/e)
    have htpos : 0<t := by
      dsimp [t]
      rw [one_div,Real.log_inv]
      exact neg_pos.mpr (Real.log_neg he (by linarith))
    have hrate : 0<mainRate e := mul_pos (div_pos (by norm_num [mainC]) he)
      (Real.rpow_pos_of_pos (by norm_num) _)
    have hp : 0<log2 ((f e).toReal) := hrate.trans_le (hl e he heE)
    have hfp : 0<(f e).toReal := by
      by_contra hh
      have hz : (f e).toReal=0 := le_antisymm (not_lt.mp hh) ENNReal.toReal_nonneg
      simp only [hz,log2,Real.log_zero,zero_div] at hp
      linarith
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hu e he he1)
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hr
    have hln := (Real.log_le_iff_le_exp hfp).mpr hr
    have hbound : log2 ((f e).toReal)≤K*(1/e)*t := by
      have hh := div_le_div_of_nonneg_right hln hL.le
      convert hh using 1 <;> dsimp [K,t,log2] <;> ring
    have hh := div_le_div_of_nonneg_right (Real.log_le_log hp hbound) htpos.le
    have hkt : Real.log (K*(1/e)*t)=Real.log K+t+Real.log t := by
      rw [Real.log_mul (mul_ne_zero hK.ne' (div_ne_zero (by norm_num) he.ne')) htpos.ne',
        Real.log_mul hK.ne' (div_ne_zero (by norm_num) he.ne')]
    rw [hkt] at hh
    have hequal : (Real.log K+t+Real.log t)/t=1+Real.log K*(1/t)+Real.log t/t := by
      rw [add_div,add_div,div_self htpos.ne']
      ring
    rw [hequal] at hh
    exact hh

end
end Blueprint.AConstants

-- ROUND-12 DECLARATION AUDIT
#print axioms Blueprint.AConstants.logDefect
#print axioms Blueprint.AConstants.logDefect_derivative
#print axioms Blueprint.AConstants.log2_linear_bound
#print axioms Blueprint.AConstants.logDefect_monotone
#print axioms Blueprint.AConstants.logDefect_lower
#print axioms Blueprint.AConstants.main_rate_ge_one
#print axioms Blueprint.AConstants.bfun_mono_small
#print axioms Blueprint.AConstants.cstar_bounds
#print axioms Blueprint.AConstants.cstar_precision_bound
#print axioms Blueprint.AConstants.cstar_coefficient
#print axioms Blueprint.AConstants.lower_constants
#print axioms Blueprint.AConstants.bfun_asymptotics
#print axioms Blueprint.AConstants.main_rate_diverges
#print axioms Blueprint.AConstants.main_rate_log_exponent
#print axioms Blueprint.AConstants.profile_squeeze
