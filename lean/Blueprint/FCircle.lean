import Blueprint.FNormal
import Blueprint.W2.SpectralAlgebra
import Blueprint.W2.AtomicMeasures
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Blueprint.FCircle
noncomputable section
open Companion Companion.Analytic MeasureTheory
open scoped BigOperators ENNReal ComplexOrder MatrixOrder
open scoped Classical
set_option maxHeartbeats 600000

abbrev Torus := AddCircle (1:ℝ)
def representative (x : Torus) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x).val
def arcDist (x y : Torus) : ℝ := 2*Real.pi*dist x y
def circleComplex (x : Torus) : ℂ := Complex.exp (((2*Real.pi*representative x:ℝ):ℂ)*Complex.I)
def haar : Measure Torus := volume
def doubling (x : Torus) : Torus := x+x
def halfTurn (x : Torus) : Torus := x+(1/2:ℝ)
def root0 (x : Torus) : Torus := (representative x/2:ℝ)
def root1 (x : Torus) : Torus := (representative x/2+1/2:ℝ)
def rootLift (mu : Measure Torus) : Measure Torus :=
  (1/2:ℝ≥0∞) • Measure.map root0 mu+(1/2:ℝ≥0∞) • Measure.map root1 mu
def lip (f : Torus → ℝ) : Prop := ∀ x y, |f x-f y|≤arcDist x y
def W1 (mu nu : Measure Torus) : ℝ := sSup {r | ∃ f : Torus → ℝ,
  lip f ∧ r=(∫ x, f x ∂mu)-(∫ x, f x ∂nu)}

theorem arcDist_le_pi (x y : Torus) : arcDist x y≤Real.pi := by
  have h := AddCircle.norm_le_half_period (p:=1) (x:=x-y) (by norm_num)
  rw [←dist_eq_norm] at h
  norm_num at h
  dsimp [arcDist]
  nlinarith [Real.pi_pos]

theorem lip_continuous (f : Torus → ℝ) (hf : lip f) : Continuous f := by
  apply (LipschitzWith.of_dist_le' (K:=2*Real.pi) ?_).continuous
  intro x y
  simpa only [Real.dist_eq,arcDist] using hf x y

theorem lip_integrable (f : Torus → ℝ) (hf : lip f) (mu : Measure Torus)
    [IsFiniteMeasure mu] : Integrable f mu := by
  have h := (lip_continuous f hf).continuousOn.integrableOn_compact isCompact_univ
    (μ:=mu)
  simpa only [integrableOn_univ] using h

theorem W1_bddAbove (mu nu : Measure Torus) (hm : IsProbabilityMeasure mu)
    (hn : IsProbabilityMeasure nu) :
    BddAbove {r | ∃ f : Torus → ℝ, lip f ∧
      r=(∫ x, f x ∂mu)-(∫ x, f x ∂nu)} := by
  refine ⟨2*Real.pi,?_⟩
  rintro r ⟨f,hf,rfl⟩
  have hb (alpha : Measure Torus) (h : IsProbabilityMeasure alpha) :
      |(∫ x, f x ∂alpha)-f 0|≤Real.pi := by
    letI := h
    have hh := norm_integral_le_of_norm_le_const (μ:=alpha)
      (f:=fun x => f x-f 0) (C:=Real.pi)
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using (hf x 0).trans (arcDist_le_pi x 0)))
    simpa [integral_sub (lip_integrable f hf alpha) (integrable_const (f 0)),
      Real.norm_eq_abs] using hh
  have hmu := (abs_le.mp (hb mu hm)).2
  have hnu := (abs_le.mp (hb nu hn)).1
  linarith

theorem W1_test_le (mu nu : Measure Torus) (hm : IsProbabilityMeasure mu)
    (hn : IsProbabilityMeasure nu) (f : Torus → ℝ) (hf : lip f) :
    (∫ x, f x ∂mu)-(∫ x, f x ∂nu)≤W1 mu nu := by
  exact le_csSup (W1_bddAbove mu nu hm hn) ⟨f,hf,rfl⟩

theorem W1_symm (mu nu : Measure Torus) (hm : IsProbabilityMeasure mu) (hn : IsProbabilityMeasure nu) :
    W1 mu nu=W1 nu mu := by
  unfold W1
  congr 1
  ext r
  have hneg (alpha beta : Measure Torus) :
      (∃ f : Torus → ℝ, lip f ∧ r=(∫ x, f x ∂alpha)-(∫ x, f x ∂beta)) →
      (∃ f : Torus → ℝ, lip f ∧ r=(∫ x, f x ∂beta)-(∫ x, f x ∂alpha)) := by
    rintro ⟨f,hf,rfl⟩
    refine ⟨fun x => -f x,?_,?_⟩
    · intro x y
      simpa only [neg_sub_neg,abs_sub_comm] using hf x y
    · simp only [integral_neg]
      ring
  exact ⟨hneg mu nu,hneg nu mu⟩
theorem W1_triangle (mu nu eta : Measure Torus) (hm : IsProbabilityMeasure mu)
    (hn : IsProbabilityMeasure nu) (he : IsProbabilityMeasure eta) : W1 mu eta≤W1 mu nu+W1 nu eta := by
  apply csSup_le
  · refine ⟨0,fun _ => 0,?_,by simp⟩
    intro x y
    simp only [sub_self,abs_zero]
    exact mul_nonneg (by positivity) dist_nonneg
  · rintro r ⟨f,hf,rfl⟩
    have h1 := W1_test_le mu nu hm hn f hf
    have h2 := W1_test_le nu eta hn he f hf
    linarith

theorem doubling_measurable : Measurable doubling :=
  (continuous_id.add continuous_id).measurable

theorem halfTurn_measurable : Measurable halfTurn :=
  (continuous_id.add continuous_const).measurable

theorem representative_measurable : Measurable representative := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco (T:=1) 0).measurable

theorem root0_measurable : Measurable root0 :=
  AddCircle.measurable_mk'.comp (representative_measurable.div_const 2)

theorem root1_measurable : Measurable root1 :=
  AddCircle.measurable_mk'.comp ((representative_measurable.div_const 2).add_const (1/2))

theorem map_probability (f : Torus → Torus) (hf : Measurable f)
    (mu : Measure Torus) (hm : IsProbabilityMeasure mu) : IsProbabilityMeasure (Measure.map f mu) := by
  letI := hm
  constructor
  rw [Measure.map_apply hf MeasurableSet.univ]
  simp

theorem haar_probability : IsProbabilityMeasure haar := by
  constructor
  change (volume : Measure Torus) Set.univ=1
  rw [AddCircle.measure_univ]
  norm_num

theorem rootLift_probability (mu : Measure Torus) (hm : IsProbabilityMeasure mu) :
    IsProbabilityMeasure (rootLift mu) := by
  letI := map_probability root0 root0_measurable mu hm
  letI := map_probability root1 root1_measurable mu hm
  constructor
  simp only [rootLift,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  have hh : (((1/2:NNReal)+(1/2:NNReal):NNReal):ℝ≥0∞)=1 := by norm_num
  simpa [ENNReal.coe_add,ENNReal.coe_div] using hh

theorem W1_to_half_mix (mu nu : Measure Torus) (hm : IsProbabilityMeasure mu)
    (hn : IsProbabilityMeasure nu) :
    W1 mu ((1/2:ℝ≥0∞) • mu+(1/2:ℝ≥0∞) • nu)≤W1 mu nu/2 := by
  letI := hm
  letI := hn
  apply csSup_le
  · refine ⟨0,fun _ => 0,?_,by simp⟩
    intro x y
    simp only [sub_self,abs_zero]
    exact mul_nonneg (by positivity) dist_nonneg
  · rintro r ⟨f,hf,rfl⟩
    have hlin : (∫ x, f x ∂((1/2:ℝ≥0∞) • mu+(1/2:ℝ≥0∞) • nu))=
        (1/2:ℝ)*(∫ x, f x ∂mu)+(1/2:ℝ)*(∫ x, f x ∂nu) := by
      rw [integral_add_measure
        ((lip_integrable f hf mu).smul_measure (by norm_num))
        ((lip_integrable f hf nu).smul_measure (by norm_num)),
        integral_smul_measure,integral_smul_measure]
      norm_num [smul_eq_mul]
    rw [hlin]
    have ht := W1_test_le mu nu hm hn f hf
    linarith

theorem representative_coe (x : Torus) : ((representative x:ℝ):Torus)=x :=
  (AddCircle.equivIco (1:ℝ) 0).symm_apply_apply x

theorem periodic_lip (g : ℝ → ℝ) (hp : Function.Periodic g 1)
    (hg : ∀ t u, |g t-g u|≤2*Real.pi*|t-u|) : lip (fun x => g (representative x)) := by
  intro x y
  let n : ℤ := round (representative x-representative y)
  have hshift : g (representative y+(n:ℝ))=g (representative y) := by
    simpa only [mul_one] using hp.int_mul n (representative y)
  have hdist : dist x y=|representative x-representative y-(n:ℝ)| := by
    conv_lhs => rw [←representative_coe x,←representative_coe y]
    rw [dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq]
    simp [n]
  have hh := hg (representative x) (representative y+(n:ℝ))
  rw [hshift] at hh
  dsimp [arcDist]
  rw [hdist]
  convert hh using 1 <;> congr 2 <;> ring

theorem roots_real_periodic {E : Type*} [AddCommMonoid E] (f : Torus → E) :
    Function.Periodic (fun t : ℝ => f ((t/2:ℝ):Torus)+f ((t/2+1/2:ℝ):Torus)) 1 := by
  intro t
  have h1 : (t+1)/2=t/2+1/2 := by ring
  have h2 : (t+1)/2+1/2=t/2+1 := by ring
  have hx : (((t+1)/2:ℝ):Torus)=((t/2+1/2:ℝ):Torus) :=
    congrArg (fun r : ℝ => (r:Torus)) h1
  have hy : (((t+1)/2:ℝ):Torus)+(1/2:ℝ)=((t/2:ℝ):Torus) := by
    rw [←AddCircle.coe_add,h2,AddCircle.coe_add_period]
  change f (((t+1)/2:ℝ):Torus)+f ((((t+1)/2:ℝ):Torus)+(1/2:ℝ))=
    f ((t/2:ℝ):Torus)+f ((t/2+1/2:ℝ):Torus)
  rw [hy,hx]
  exact add_comm _ _

theorem periodic_representative {E : Type*} (g : ℝ → E) (hp : Function.Periodic g 1) (t : ℝ) :
    g (representative (t:Torus))=g t := by
  have hz : (((representative (t:Torus)-t:ℝ)):Torus)=0 := by
    rw [AddCircle.coe_sub,representative_coe,sub_self]
  have hm : representative (t:Torus)-t∈AddSubgroup.zmultiples (1:ℝ) :=
    (QuotientAddGroup.eq_zero_iff _).mp hz
  obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  simp only [zsmul_eq_mul,mul_one] at hn
  have ht : representative (t:Torus)=t+(n:ℝ) := by linarith
  rw [ht]
  simpa only [mul_one] using hp.int_mul n t

theorem roots_doubling_sum {E : Type*} [AddCommMonoid E] (f : Torus → E) (x : Torus) :
    f (root0 (doubling x))+f (root1 (doubling x))=f x+f (halfTurn x) := by
  let g : ℝ → E := fun t => f ((t/2:ℝ):Torus)+f ((t/2+1/2:ℝ):Torus)
  have hx : ((2*representative x:ℝ):Torus)=doubling x := by
    rw [two_mul,AddCircle.coe_add,representative_coe]
    rfl
  have he := periodic_representative g (roots_real_periodic f) (2*representative x)
  rw [hx] at he
  change g (representative (doubling x))=f x+f (halfTurn x)
  rw [he]
  change f (((2*representative x)/2:ℝ):Torus)+
    f (((2*representative x)/2+1/2:ℝ):Torus)=_
  rw [show (2*representative x)/2=representative x by ring]
  simp only [AddCircle.coe_add,representative_coe]
  rfl

theorem roots_sum_lip (f : Torus → ℝ) (hf : lip f) :
    lip (fun x => f (root0 x)+f (root1 x)) := by
  let g : ℝ → ℝ := fun t => f ((t/2:ℝ):Torus)+f ((t/2+1/2:ℝ):Torus)
  have hp : Function.Periodic g 1 := roots_real_periodic f
  have hcoe (t u : ℝ) : dist (t:Torus) (u:Torus)≤|t-u| := by
    rw [dist_eq_norm,←AddCircle.coe_sub]
    simpa only [Real.norm_eq_abs] using
      (QuotientAddGroup.norm_mk_le_norm (S:=AddSubgroup.zmultiples (1:ℝ)) (m:=t-u))
  have hg (t u : ℝ) : |g t-g u|≤2*Real.pi*|t-u| := by
    have hbranch (v : ℝ) :
        |f ((t/2+v:ℝ):Torus)-f ((u/2+v:ℝ):Torus)|≤Real.pi*|t-u| := by
      calc
        _≤2*Real.pi*dist ((t/2+v:ℝ):Torus) ((u/2+v:ℝ):Torus) := hf _ _
        _≤2*Real.pi*|(t/2+v)-(u/2+v)| :=
          mul_le_mul_of_nonneg_left (hcoe _ _) (by positivity)
        _=Real.pi*|t-u| := by
          rw [show (t/2+v)-(u/2+v)=(t-u)/2 by ring,abs_div]
          norm_num
          ring
    have h0 := hbranch 0
    have h1 := hbranch (1/2)
    simp only [add_zero] at h0
    calc
      _=|(f ((t/2:ℝ):Torus)-f ((u/2:ℝ):Torus))+
          (f ((t/2+1/2:ℝ):Torus)-f ((u/2+1/2:ℝ):Torus))| := by dsimp [g]; congr 1; ring
      _≤|f ((t/2:ℝ):Torus)-f ((u/2:ℝ):Torus)|+
          |f ((t/2+1/2:ℝ):Torus)-f ((u/2+1/2:ℝ):Torus)| := abs_add_le _ _
      _≤_ := by linarith
  exact periodic_lip g hp hg

theorem rootLift_integral (mu : Measure Torus) (hm : IsProbabilityMeasure mu)
    (f : Torus → ℝ) (hf : lip f) :
    (∫ x, f x ∂rootLift mu)=(1/2:ℝ)*(∫ x, (f (root0 x)+f (root1 x)) ∂mu) := by
  letI := map_probability root0 root0_measurable mu hm
  letI := map_probability root1 root1_measurable mu hm
  have h0 := lip_integrable f hf (Measure.map root0 mu)
  have h1 := lip_integrable f hf (Measure.map root1 mu)
  rw [rootLift,integral_add_measure (h0.smul_measure (by norm_num)) (h1.smul_measure (by norm_num)),
    integral_smul_measure,integral_smul_measure,
    integral_map root0_measurable.aemeasurable h0.aestronglyMeasurable,
    integral_map root1_measurable.aemeasurable h1.aestronglyMeasurable]
  have hi0 : Integrable (fun x => f (root0 x)) mu := h0.comp_measurable root0_measurable
  have hi1 : Integrable (fun x => f (root1 x)) mu := h1.comp_measurable root1_measurable
  rw [integral_add hi0 hi1]
  norm_num [smul_eq_mul]
  ring

theorem root_contraction (mu nu : Measure Torus) (hm : IsProbabilityMeasure mu) (hn : IsProbabilityMeasure nu) :
    W1 (rootLift mu) (rootLift nu)≤W1 mu nu/2 := by
  apply csSup_le
  · refine ⟨0,fun _ => 0,?_,by simp⟩
    intro x y
    simp only [sub_self,abs_zero]
    exact mul_nonneg (by positivity) dist_nonneg
  · rintro r ⟨f,hf,rfl⟩
    rw [rootLift_integral mu hm f hf,rootLift_integral nu hn f hf]
    have htest := W1_test_le mu nu hm hn (fun x => f (root0 x)+f (root1 x)) (roots_sum_lip f hf)
    linarith

theorem root_doubling (mu : Measure Torus) (hm : IsProbabilityMeasure mu) :
    rootLift (Measure.map doubling mu)=(1/2:ℝ≥0∞) • mu+(1/2:ℝ≥0∞) • Measure.map halfTurn mu := by
  apply Measure.ext_of_lintegral
  intro f hf
  simp only [rootLift,lintegral_add_measure,lintegral_smul_measure,smul_eq_mul]
  rw [lintegral_map hf root0_measurable,lintegral_map hf root1_measurable,
    lintegral_map (f:=fun x => f (root0 x)) (hf.comp root0_measurable) doubling_measurable,
    lintegral_map (f:=fun x => f (root1 x)) (hf.comp root1_measurable) doubling_measurable,
    lintegral_map hf halfTurn_measurable,←mul_add,←mul_add]
  have hleft := lintegral_add_left (μ:=mu)
    (f:=fun x => f (root0 (doubling x)))
    (hf.comp (root0_measurable.comp doubling_measurable)) (fun x => f (root1 (doubling x)))
  have hright := lintegral_add_left (μ:=mu) hf (fun x => f (halfTurn x))
  rw [←hleft,←hright]
  congr 1
  exact lintegral_congr (roots_doubling_sum f)

theorem root_haar : rootLift haar=haar := by
  have hd : Measure.map doubling haar=haar := by
    change Measure.map (fun x : Torus => x+x) volume=volume
    simpa only [two_zsmul] using
      (Measure.measurePreserving_zsmul (volume : Measure Torus) (by norm_num : (2:ℤ)≠0)).map_eq
  have hh : Measure.map halfTurn haar=haar := by
    exact (measurePreserving_add_right (volume : Measure Torus) ((1/2:ℝ):Torus)).map_eq
  have hr := root_doubling haar haar_probability
  rw [hd,hh,←add_smul] at hr
  have hhalf : (1/2:ℝ≥0∞)+(1/2:ℝ≥0∞)=1 := by
    have h : (((1/2:NNReal)+(1/2:NNReal):NNReal):ℝ≥0∞)=1 := by norm_num
    simpa [ENNReal.coe_add,ENNReal.coe_div] using h
  simpa only [hhalf,one_smul] using hr

theorem haar_comparison (mu : Measure Torus) (hm : IsProbabilityMeasure mu) :
    W1 mu haar≤W1 (Measure.map doubling mu) mu+W1 (Measure.map halfTurn mu) mu := by
  have hd := map_probability doubling doubling_measurable mu hm
  have hh := map_probability halfTurn halfTurn_measurable mu hm
  have hP := rootLift_probability mu hm
  have hPD := rootLift_probability (Measure.map doubling mu) hd
  have h1 := W1_triangle mu (rootLift (Measure.map doubling mu)) haar hm hPD haar_probability
  have h2 := W1_triangle (rootLift (Measure.map doubling mu)) (rootLift mu) haar hPD hP haar_probability
  have hmix := W1_to_half_mix mu (Measure.map halfTurn mu) hm hh
  rw [←root_doubling mu hm,W1_symm mu (Measure.map halfTurn mu) hm hh] at hmix
  have hdouble := root_contraction (Measure.map doubling mu) mu hd hm
  have hhaar := root_contraction mu haar hm haar_probability
  rw [root_haar] at hhaar
  linarith
theorem atomic_obstruction (d : Nat) (hd : 0<d) (mu : Measure Torus) (hm : IsProbabilityMeasure mu)
    (S : Finset Torus) (hS : S.card≤d) (hs : mu (S:Set Torus)ᶜ=0) :
    Real.pi/(2*d)≤W1 mu haar := by
  letI := hm
  letI := haar_probability
  have hSne : S.Nonempty := by
    by_contra h
    have hEmpty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simpa only [hEmpty,Finset.coe_empty,Set.compl_empty,measure_univ,one_ne_zero] using hs
  have hSet : (S:Set Torus).Nonempty := hSne
  let D : Torus → ℝ := fun x => Metric.infDist x (S:Set Torus)
  have hDlip : LipschitzWith 1 D := Metric.lipschitz_infDist_pt _
  have hDcont : Continuous D := hDlip.continuous
  have hD0 (x : Torus) : 0≤D x := Metric.infDist_nonneg
  have hDsmall (x : Torus) : D x≤(1/2:ℝ) := by
    obtain ⟨a,ha⟩ := hSne
    have hdist := AddCircle.norm_le_half_period (p:=1) (x:=x-a) (by norm_num)
    rw [←dist_eq_norm] at hdist
    norm_num at hdist
    exact (Metric.infDist_le_dist_of_mem ha).trans hdist
  have hDi : Integrable D haar := by
    simpa only [integrableOn_univ] using
      hDcont.continuousOn.integrableOn_compact isCompact_univ (μ:=haar)
  let F : ℝ → ℝ := fun t => haar.real {x | t≤D x}
  have hFanti : Antitone F := by
    intro a b hab
    exact measureReal_mono (fun x hx => hab.trans hx)
  have hF0 (t : ℝ) : 0≤F t := measureReal_nonneg
  have hFbound (t : ℝ) : ‖F t‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hF0 t)]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  have hFi : IntegrableOn F (Set.Ioc (0:ℝ) (1/2)) :=
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      hFanti.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hFbound)
  have hTail (t : ℝ) (ht : 0≤t) : 1-2*(d:ℝ)*t≤F t := by
    have hcover : {x | D x<t}⊆⋃ a∈S, Metric.closedBall a t := by
      intro x hx
      obtain ⟨a,ha,hax⟩ := (Metric.infDist_lt_iff hSet).mp hx
      exact Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨ha,hax.le⟩⟩
    have hball (a : Torus) : haar.real (Metric.closedBall a t)≤2*t := by
      change ((volume : Measure Torus) (Metric.closedBall a t)).toReal≤2*t
      rw [AddCircle.volume_closedBall,ENNReal.toReal_ofReal
        (le_min zero_le_one (mul_nonneg zero_le_two ht))]
      exact min_le_right _ _
    have hUpper : haar.real {x | D x<t}≤(S.card:ℝ)*(2*t) := by
      calc
        _≤haar.real (⋃ a∈S, Metric.closedBall a t) := measureReal_mono hcover (measure_ne_top _ _)
        _≤∑ a∈S, haar.real (Metric.closedBall a t) := measureReal_biUnion_finset_le S _
        _≤∑ _a∈S, 2*t := Finset.sum_le_sum (fun a _ => hball a)
        _=_ := by simp
    have hMeas : MeasurableSet {x | D x<t} := (isOpen_lt hDcont continuous_const).measurableSet
    have hcompl : {x | t≤D x}={x | D x<t}ᶜ := by ext x; simp
    dsimp [F]
    rw [hcompl,measureReal_compl hMeas,probReal_univ]
    have hcard : (S.card:ℝ)≤d := by exact_mod_cast hS
    nlinarith [mul_le_mul_of_nonneg_right hcard (mul_nonneg zero_le_two ht)]
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  let R : ℝ := 1/(2*d)
  have hR : 0<R := by dsimp [R]; positivity
  have hRsmall : R≤(1/2:ℝ) := by
    dsimp [R]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*d)).mpr
    nlinarith
  have hSub : Set.Ioc (0:ℝ) R⊆Set.Ioc 0 (1/2) :=
    fun x hx => ⟨hx.1,hx.2.trans hRsmall⟩
  have hLi : IntegrableOn (fun t : ℝ => 1-2*(d:ℝ)*t) (Set.Ioc 0 R) := by
    exact ((continuous_const.sub (continuous_const.mul continuous_id)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hLinear : (∫ t in Set.Ioc (0:ℝ) R, (1-2*(d:ℝ)*t))=1/(4*d) := by
    have hcont : Continuous (fun x : ℝ => 2*(d:ℝ)*x) := continuous_const.mul continuous_id
    rw [←intervalIntegral.integral_of_le hR.le,
      intervalIntegral.integral_sub (f:=fun _ : ℝ => (1:ℝ))
        (g:=fun x : ℝ => 2*(d:ℝ)*x) (continuous_const.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
    dsimp [R]
    simp only [sub_zero,zero_pow (by decide : (2:Nat)≠0),smul_eq_mul,mul_one]
    field_simp
    ring
  have hLayer : (∫ x, D x ∂haar)=∫ t in Set.Ioc (0:ℝ) (1/2), F t :=
    hDi.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall hD0) (Filter.Eventually.of_forall hDsmall)
  have hQuant : 1/(4*(d:ℝ))≤∫ x, D x ∂haar := by
    calc
      _=∫ t in Set.Ioc (0:ℝ) R, (1-2*(d:ℝ)*t) := hLinear.symm
      _≤∫ t in Set.Ioc (0:ℝ) R, F t :=
        setIntegral_mono_on hLi (hFi.mono_set hSub) measurableSet_Ioc
          (fun t ht => hTail t ht.1.le)
      _≤∫ t in Set.Ioc (0:ℝ) (1/2), F t :=
        setIntegral_mono_set hFi (Filter.Eventually.of_forall hF0)
          (Filter.Eventually.of_forall (fun x hx => hSub hx))
      _=_ := hLayer.symm
  let f : Torus → ℝ := fun x => -(2*Real.pi)*D x
  have hf : lip f := by
    intro x y
    have hh := hDlip.dist_le_mul x y
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hh
    rw [show f x-f y= -(2*Real.pi)*(D x-D y) by dsimp [f]; ring,
      abs_mul,abs_neg,abs_of_pos (by positivity : (0:ℝ)<2*Real.pi)]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hmem : ∀ᵐ x ∂mu, x∈(S:Set Torus) := by
    rw [ae_iff]
    exact hs
  have hfzero : (∫ x, f x ∂mu)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hmem] with x hx
    change f x=0
    simp only [f,D,Metric.infDist_zero_of_mem hx,mul_zero]
  have hfhaar : (∫ x, f x ∂haar)= -(2*Real.pi)*(∫ x, D x ∂haar) := integral_const_mul _ _
  have hW := W1_test_le mu haar hm haar_probability f hf
  rw [hfzero,hfhaar] at hW
  have hscale := mul_le_mul_of_nonneg_left hQuant (by positivity : (0:ℝ)≤2*Real.pi)
  have heq : (2*Real.pi)*(1/(4*(d:ℝ)))=Real.pi/(2*d) := by ring
  rw [heq] at hscale
  linarith

theorem spectral_resolution {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    ∃ q : Mat d × (Fin d → ℂ), IsUnitary q.1 ∧ (∀ i, ‖q.2 i‖=1) ∧
      U=q.1*Matrix.diagonal q.2*q.1.conjTranspose := FNormal.diagonalize U hU
def spectralData {d : Nat} (U : Mat d) (hU : IsUnitary U) : Mat d × (Fin d → ℂ) :=
  Classical.choose (spectral_resolution U hU)

theorem spectralData_properties {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    IsUnitary (spectralData U hU).1 ∧ (∀ i, ‖(spectralData U hU).2 i‖=1) ∧
      U=(spectralData U hU).1*Matrix.diagonal (spectralData U hU).2*
        (spectralData U hU).1.conjTranspose := Classical.choose_spec (spectral_resolution U hU)
def spectralMeasure {d : Nat} (U : Mat d) (hU : IsUnitary U) (s : State d) : Measure Torus :=
  let q := spectralData U hU
  ∑ i, ENNReal.ofReal ((q.1.conjTranspose*s.rho*q.1) i i).re •
    Measure.dirac (((Complex.arg (q.2 i)/(2*Real.pi)):ℝ):Torus)

theorem spectral_probability {d : Nat} (U : Mat d) (hU : IsUnitary U) (s : State d) :
    IsProbabilityMeasure (spectralMeasure U hU s) := by
  let V := (spectralData U hU).1
  have hV := (spectralData_properties U hU).1
  have hpos := s.positive.conjTranspose_mul_mul_same V
  have hp (i : Fin d) : 0≤((V.conjTranspose*s.rho*V) i i).re := by
    exact (hpos.diag_nonneg (i:=i)).1
  have ht : (V.conjTranspose*s.rho*V).trace=1 := by
    rw [Matrix.trace_mul_cycle,hV.2,Matrix.one_mul,s.normalized]
  have ht' : (∑ i, ((V.conjTranspose*s.rho*V) i i).re)=1 := by
    have hh := congrArg Complex.re ht
    simpa [Matrix.trace,Matrix.diag_apply] using hh
  constructor
  simp only [spectralMeasure,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply,Set.indicator_univ,Pi.one_apply,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i),ht']
  norm_num
theorem spectral_support {d : Nat} (U : Mat d) (hU : IsUnitary U) (s : State d) :
    ∃ S : Finset Torus, S.card≤d ∧ spectralMeasure U hU s (S:Set Torus)ᶜ=0 := by
  classical
  let f : Fin d → Torus := fun i =>
    (((Complex.arg ((spectralData U hU).2 i)/(2*Real.pi)):ℝ):Torus)
  refine ⟨Finset.univ.image f,?_,?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · simp only [spectralMeasure,Measure.finsetSum_apply,Measure.smul_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi : f i∉(Finset.univ.image f:Set Torus)ᶜ := by simp
    rw [Measure.dirac_apply,Set.indicator_of_notMem hi,smul_zero]
def eigenAngle (z : ℂ) : Torus := ((Complex.arg z/(2*Real.pi):ℝ):Torus)

def resolutionMeasure {d : Nat} (V : Mat d) (z : Fin d → ℂ) (s : State d) : Measure Torus :=
  ∑ i, ENNReal.ofReal ((V.conjTranspose*s.rho*V) i i).re • Measure.dirac (eigenAngle (z i))

theorem resolution_weight_nonnegative {d : Nat} (V : Mat d) (s : State d) (i : Fin d) :
    0≤((V.conjTranspose*s.rho*V) i i).re :=
  ((s.positive.conjTranspose_mul_mul_same V).diag_nonneg (i:=i)).1

theorem resolutionMeasure_apply {d : Nat} (V : Mat d) (z : Fin d → ℂ) (s : State d)
    (B : Set Torus) (hB : MeasurableSet B) :
    resolutionMeasure V z s B=ENNReal.ofReal
      (∑ i, if eigenAngle (z i)∈B then ((V.conjTranspose*s.rho*V) i i).re else 0) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    split
    · exact resolution_weight_nonnegative V s i
    · exact le_rfl)]
  simp only [resolutionMeasure,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : eigenAngle (z i)∈B <;> simp [hi]

theorem resolutionMeasure_unique {d : Nat} (U V W : Mat d) (z w : Fin d → ℂ)
    (s : State d) (hV : IsUnitary V) (hW : IsUnitary W)
    (hz : U=V*Matrix.diagonal z*V.conjTranspose)
    (hw : U=W*Matrix.diagonal w*W.conjTranspose) :
    resolutionMeasure V z s=resolutionMeasure W w s := by
  classical
  ext B hB
  rw [resolutionMeasure_apply V z s B hB,resolutionMeasure_apply W w s B hB]
  congr 1
  have h := W2.spectral_weighted_sum U V W s.rho z w hV hW hz hw
    (fun v => if eigenAngle v∈B then (1:ℂ) else 0)
  have hr := congrArg Complex.re h
  simpa only [mul_ite,mul_one,mul_zero,Complex.re_sum,apply_ite,Complex.zero_re] using hr

theorem spectralMeasure_eq_resolution {d : Nat} (U V : Mat d) (hU : IsUnitary U)
    (z : Fin d → ℂ) (s : State d) (hV : IsUnitary V)
    (hz : U=V*Matrix.diagonal z*V.conjTranspose) :
    spectralMeasure U hU s=resolutionMeasure V z s := by
  have hp := spectralData_properties U hU
  exact resolutionMeasure_unique U (spectralData U hU).1 V (spectralData U hU).2 z s hp.1 hV hp.2.2 hz

def angleScale : Real.Angle ≃+ Torus :=
  AddCircle.equivAddCircle (2*Real.pi) 1 (by positivity) (by norm_num)

theorem angleScale_coe (r : ℝ) : angleScale (r:Real.Angle)=((r/(2*Real.pi):ℝ):Torus) := by
  change AddCircle.equivAddCircle (2*Real.pi) 1 _ _ (r:AddCircle (2*Real.pi))= _
  rw [AddCircle.equivAddCircle_apply_mk]
  congr 1
  ring

theorem eigenAngle_square (z : ℂ) : eigenAngle (z*z)=doubling (eigenAngle z) := by
  calc
    _=angleScale (Complex.arg (z^2):Real.Angle) := by rw [angleScale_coe,pow_two]; rfl
    _=angleScale (2 • (Complex.arg z:Real.Angle)) := by rw [Complex.arg_pow_coe_angle]
    _=_ := by rw [map_nsmul,two_nsmul,angleScale_coe]; rfl

theorem eigenAngle_negative (z : ℂ) (hz : z≠0) : eigenAngle (-z)=halfTurn (eigenAngle z) := by
  have hpi : Real.pi/(2*Real.pi)=(1/2:ℝ) := by field_simp
  calc
    _=angleScale (Complex.arg (-z):Real.Angle) := (angleScale_coe _).symm
    _=angleScale ((Complex.arg z:Real.Angle)+(Real.pi:Real.Angle)) := by
      rw [Complex.arg_neg_coe_angle hz]
    _=_ := by rw [map_add,angleScale_coe,angleScale_coe,hpi]; rfl

theorem resolutionMeasure_map {d : Nat} (V : Mat d) (z w : Fin d → ℂ) (s : State d)
    (f : Torus → Torus) (hf : Measurable f) (hw : ∀ i, eigenAngle (w i)=f (eigenAngle (z i))) :
    resolutionMeasure V w s=Measure.map f (resolutionMeasure V z s) := by
  ext B hB
  rw [Measure.map_apply hf hB,resolutionMeasure_apply V w s B hB,
    resolutionMeasure_apply V z s (f ⁻¹' B) (hf hB)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hw i]
  rfl

theorem resolutionMeasure_integral {d : Nat} (V : Mat d) (z : Fin d → ℂ) (s : State d)
    (f : Torus → ℝ) :
    (∫ x, f x ∂resolutionMeasure V z s)=
      ∑ i, ((V.conjTranspose*s.rho*V) i i).re*f (eigenAngle (z i)) := by
  have hi (i : Fin d) : Integrable f
      (ENNReal.ofReal ((V.conjTranspose*s.rho*V) i i).re • Measure.dirac (eigenAngle (z i))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [resolutionMeasure,integral_finsetSum_measure (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (resolution_weight_nonnegative V s i)]
  rfl

theorem lip_center (f : Torus → ℝ) (hf : lip f) :
    ∃ c : ℝ, ∀ x, |f x-c|≤Real.pi/2 := by
  obtain ⟨a,_,ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty (lip_continuous f hf).continuousOn
  obtain ⟨b,_,hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty (lip_continuous f hf).continuousOn
  refine ⟨(f a+f b)/2,?_⟩
  intro x
  have hmin := ha (Set.mem_univ x)
  have hmax := hb (Set.mem_univ x)
  change f a≤f x at hmin
  change f x≤f b at hmax
  have hwidth : f b-f a≤Real.pi := (le_abs_self _).trans ((hf b a).trans (arcDist_le_pi b a))
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem spectral_square {d : Nat} (U : Mat d) (hU : IsUnitary U) (s : State d) :
    spectralMeasure (U*U) (ReturnProof.unitary_mul U U hU hU) s=
      Measure.map doubling (spectralMeasure U hU s) := by
  let V := (spectralData U hU).1
  let z := (spectralData U hU).2
  have hp := spectralData_properties U hU
  have hdiag : U*U=V*Matrix.diagonal (fun i => z i*z i)*V.conjTranspose := by
    rw [hp.2.2]
    change (V*Matrix.diagonal z*V.conjTranspose)*(V*Matrix.diagonal z*V.conjTranspose)=_
    calc
      _=V*Matrix.diagonal z*(V.conjTranspose*V)*Matrix.diagonal z*V.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _=V*(Matrix.diagonal z*Matrix.diagonal z)*V.conjTranspose := by
        rw [hp.1.1,Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _=_ := by rw [Matrix.diagonal_mul_diagonal]
  rw [spectralMeasure_eq_resolution (U*U) V _ _ s hp.1 hdiag,
    spectralMeasure_eq_resolution U V hU z s hp.1 hp.2.2]
  exact resolutionMeasure_map V z (fun i => z i*z i) s doubling doubling_measurable
    (fun i => eigenAngle_square (z i))
theorem spectral_negative {d : Nat} (U : Mat d) (hU : IsUnitary U) (s : State d)
    (hneg : IsUnitary (-U)) : spectralMeasure (-U) hneg s=Measure.map halfTurn (spectralMeasure U hU s) := by
  let V := (spectralData U hU).1
  let z := (spectralData U hU).2
  have hp := spectralData_properties U hU
  have hdiag : -U=V*Matrix.diagonal (fun i => -z i)*V.conjTranspose := by
    rw [hp.2.2,←Matrix.diagonal_neg,Matrix.mul_neg,Matrix.neg_mul]
  rw [spectralMeasure_eq_resolution (-U) V hneg _ s hp.1 hdiag,
    spectralMeasure_eq_resolution U V hU z s hp.1 hp.2.2]
  apply resolutionMeasure_map V z (fun i => -z i) s halfTurn halfTurn_measurable
  intro i
  apply eigenAngle_negative
  exact norm_ne_zero_iff.mp (by rw [hp.2.1 i]; norm_num)

theorem spectral_conjugation {d : Nat} (U Y : Mat d) (hU : IsUnitary U) (hY : IsUnitary Y)
    (s t : State d) (ht : t.rho=U.conjTranspose*s.rho*U) :
    spectralMeasure (U*Y*U.conjTranspose)
      (ReturnProof.unitary_mul _ _ (ReturnProof.unitary_mul _ _ hU hY) (ReturnProof.unitary_adjoint U hU)) s=
      spectralMeasure Y hY t := by
  let V := (spectralData Y hY).1
  let z := (spectralData Y hY).2
  have hp := spectralData_properties Y hY
  have hUV : IsUnitary (U*V) := ReturnProof.unitary_mul U V hU hp.1
  have hdiag : U*Y*U.conjTranspose=(U*V)*Matrix.diagonal z*(U*V).conjTranspose := by
    rw [hp.2.2,Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rfl
  rw [spectralMeasure_eq_resolution _ (U*V) _ z s hUV hdiag,
    spectralMeasure_eq_resolution Y V hY z t hp.1 hp.2.2]
  have hweight : (U*V).conjTranspose*s.rho*(U*V)=V.conjTranspose*t.rho*V := by
    rw [ht,Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp only [resolutionMeasure,hweight]

def circlePhase (t : ℝ) : ℂ := Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I)

theorem circlePhase_add (t u : ℝ) : circlePhase (t+u)=circlePhase t*circlePhase u := by
  unfold circlePhase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem circlePhase_one : circlePhase 1=1 := by
  norm_num [circlePhase,Complex.exp_mul_I]

theorem circlePhase_periodic : Function.Periodic circlePhase 1 := by
  intro t
  rw [circlePhase_add,circlePhase_one,mul_one]

theorem circleComplex_coe (t : ℝ) : circleComplex (t:Torus)=circlePhase t :=
  periodic_representative circlePhase circlePhase_periodic t

theorem circlePhase_norm (t : ℝ) : ‖circlePhase t‖=1 :=
  Complex.norm_exp_ofReal_mul_I (2*Real.pi*t)

theorem circleComplex_eigenAngle (z : ℂ) (hz : ‖z‖=1) : circleComplex (eigenAngle z)=z := by
  rw [eigenAngle,circleComplex_coe]
  unfold circlePhase
  rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ)≠0)]
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz,Complex.ofReal_one,one_mul] at h
  exact h

theorem circlePhase_sub_norm (t u : ℝ) :
    ‖circlePhase t-circlePhase u‖=2*|Real.sin (Real.pi*(t-u))| := by
  have he : circlePhase t-circlePhase u=(circlePhase (t-u)-1)*circlePhase u := by
    rw [sub_mul,one_mul,←circlePhase_add,sub_add_cancel]
  rw [he,norm_mul,circlePhase_norm,mul_one]
  change ‖Complex.exp (((2*Real.pi*(t-u):ℝ):ℂ)*Complex.I)-1‖=_
  rw [mul_comm (_:ℂ) Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2*Real.pi*(t-u))/2=Real.pi*(t-u) by ring,Real.norm_eq_abs,abs_mul]
  norm_num

theorem arcDist_le_chord (x y : Torus) :
    arcDist x y≤Real.pi/2*‖circleComplex x-circleComplex y‖ := by
  let n : ℤ := round (representative x-representative y)
  let v : ℝ := representative x-representative y-(n:ℝ)
  have hsmall : |v|≤(1/2:ℝ) := by exact abs_sub_round _
  have hdist : dist x y=|v| := by
    conv_lhs => rw [←representative_coe x,←representative_coe y]
    rw [dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq]
    simp [v,n]
  have hshift : circlePhase (representative y+(n:ℝ))=circlePhase (representative y) := by
    simpa only [mul_one] using circlePhase_periodic.int_mul n (representative y)
  have hchord : ‖circleComplex x-circleComplex y‖=2*|Real.sin (Real.pi*v)| := by
    change ‖circlePhase (representative x)-circlePhase (representative y)‖=_
    rw [←hshift,circlePhase_sub_norm]
    congr 3
    dsimp [v]
    ring
  have hangle : |Real.pi*v|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left hsmall Real.pi_pos.le]
  have hsin := Real.mul_abs_le_abs_sin hangle
  rw [abs_mul,abs_of_pos Real.pi_pos] at hsin
  have hsin' : 2*|v|≤|Real.sin (Real.pi*v)| := by
    convert hsin using 1
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hsin' Real.pi_pos.le
  rw [arcDist,hdist,hchord]
  nlinarith only [hscaled]

theorem coupling {d : Nat} (P Q : Mat d) (hP : IsUnitary P) (hQ : IsUnitary Q) (s : State d) :
    ∃ nu : Measure (Torus × Torus), IsProbabilityMeasure nu ∧
      Measure.map Prod.fst nu=spectralMeasure P hP s ∧ Measure.map Prod.snd nu=spectralMeasure Q hQ s ∧
      (∫ z, ‖circleComplex z.1-circleComplex z.2‖^2 ∂nu)=hs (P*s.xi-s.xi*Q)^2 ∧
      W1 (spectralMeasure P hP s) (spectralMeasure Q hQ s)≤Real.pi/2*hs (P*s.xi-s.xi*Q) := by
  let V := (spectralData P hP).1
  let W := (spectralData Q hQ).1
  let z := (spectralData P hP).2
  let w := (spectralData Q hQ).2
  have hp := spectralData_properties P hP
  have hq := spectralData_properties Q hQ
  let B := V.conjTranspose*s.xi*W
  let wt := fun i j => Complex.normSq (B i j)
  let nu : Measure (Torus × Torus) := W2.atomicMeasure
    (fun ij : Fin d × Fin d => wt ij.1 ij.2) (fun ij => (eigenAngle (z ij.1),eigenAngle (w ij.2)))
  have hw0 (i j : Fin d) : 0≤wt i j := Complex.normSq_nonneg _
  have hrow (i : Fin d) : (∑ j, wt i j)=((V.conjTranspose*s.rho*V) i i).re := by
    dsimp [wt]
    rw [W2.row_normSq]
    change (((V.conjTranspose*s.xi*W)*(V.conjTranspose*s.xi*W).conjTranspose) i i).re=_
    rw [W2.state_factor_rows V W hq.1 s]
  have hcol (j : Fin d) : (∑ i, wt i j)=((W.conjTranspose*s.rho*W) j j).re := by
    dsimp [wt]
    rw [W2.col_normSq]
    change (((V.conjTranspose*s.xi*W).conjTranspose*(V.conjTranspose*s.xi*W)) j j).re=_
    rw [W2.state_factor_cols V W hp.1 s]
  have hsum : (∑ i, ∑ j, wt i j)=1 := by
    simp_rw [hrow]
    have ht : (V.conjTranspose*s.rho*V).trace=1 := by
      rw [Matrix.trace_mul_cycle,hp.1.2,Matrix.one_mul,s.normalized]
    simpa only [Matrix.trace,Matrix.diag_apply,Complex.re_sum,Complex.one_re] using congrArg Complex.re ht
  have hprob : IsProbabilityMeasure nu := by
    exact W2.atomic_probability (fun ij : Fin d × Fin d => wt ij.1 ij.2)
      (fun ij => (eigenAngle (z ij.1),eigenAngle (w ij.2))) (fun ij => hw0 ij.1 ij.2)
      (by simpa only [Fintype.sum_prod_type] using hsum)
  have hfst : Measure.map Prod.fst nu=spectralMeasure P hP s := by
    rw [spectralMeasure_eq_resolution P V hP z s hp.1 hp.2.2]
    change Measure.map Prod.fst (W2.atomicMeasure (fun ij : Fin d × Fin d => wt ij.1 ij.2)
      (fun ij => (eigenAngle (z ij.1),eigenAngle (w ij.2))))=resolutionMeasure V z s
    rw [W2.atomic_fst wt (fun i => eigenAngle (z i)) (fun j => eigenAngle (w j)) hw0]
    simp only [W2.atomicMeasure,resolutionMeasure,hrow]
  have hsnd : Measure.map Prod.snd nu=spectralMeasure Q hQ s := by
    rw [spectralMeasure_eq_resolution Q W hQ w s hq.1 hq.2.2]
    change Measure.map Prod.snd (W2.atomicMeasure (fun ij : Fin d × Fin d => wt ij.1 ij.2)
      (fun ij => (eigenAngle (z ij.1),eigenAngle (w ij.2))))=resolutionMeasure W w s
    rw [W2.atomic_snd wt (fun i => eigenAngle (z i)) (fun j => eigenAngle (w j)) hw0]
    simp only [W2.atomicMeasure,resolutionMeasure,hcol]
  have hint (f : Torus × Torus → ℝ) :
      (∫ p, f p ∂nu)=∑ i, ∑ j, wt i j*f (eigenAngle (z i),eigenAngle (w j)) := by
    simpa only [Fintype.sum_prod_type] using W2.atomic_integral
      (fun ij : Fin d × Fin d => wt ij.1 ij.2)
      (fun ij => (eigenAngle (z ij.1),eigenAngle (w ij.2))) (fun ij => hw0 ij.1 ij.2) f
  have hzphase (i : Fin d) : circleComplex (eigenAngle (z i))=z i :=
    circleComplex_eigenAngle _ (hp.2.1 i)
  have hwphase (j : Fin d) : circleComplex (eigenAngle (w j))=w j :=
    circleComplex_eigenAngle _ (hq.2.1 j)
  have hcost0 := W2.spectral_cost P Q V W z w s hp.1 hq.1 hp.2.2 hq.2.2
  have hcost : (∫ p, ‖circleComplex p.1-circleComplex p.2‖^2 ∂nu)=hs (P*s.xi-s.xi*Q)^2 := by
    rw [hint,hcost0]
    simp only [hzphase,hwphase,wt]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.normSq_eq_norm_sq]
    ring
  let mean := ∑ i, ∑ j, wt i j*‖z i-w j‖
  have hmean0 : 0≤mean := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hw0 i j) (norm_nonneg _)))
  have hmass : (∑ i, ∑ j, ‖B i j‖^2)=1 := by
    simpa only [wt,Complex.normSq_eq_norm_sq] using hsum
  have hleft : (∑ i, ∑ j, ‖B i j‖*(‖B i j‖*‖z i-w j‖))=mean := by
    dsimp [mean,wt]
    simp only [Complex.normSq_eq_norm_sq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright : (∑ i, ∑ j, (‖B i j‖*‖z i-w j‖)^2)=hs (P*s.xi-s.xi*Q)^2 := by
    rw [hcost0]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.normSq_eq_norm_sq,mul_pow]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ)
    (f:=fun ij : Fin d × Fin d => ‖B ij.1 ij.2‖)
    (g:=fun ij : Fin d × Fin d => ‖B ij.1 ij.2‖*‖z ij.1-w ij.2‖)
  simp only [Fintype.sum_prod_type,hleft,hmass,hright,one_mul] at hcs
  have hmean : mean≤hs (P*s.xi-s.xi*Q) :=
    (sq_le_sq₀ hmean0 (show 0≤hs (P*s.xi-s.xi*Q) from hsNorm_nonneg _)).mp hcs
  refine ⟨nu,hprob,hfst,hsnd,hcost,?_⟩
  apply csSup_le
  · refine ⟨0,fun _ => 0,?_,by simp⟩
    intro x y
    simp only [sub_self,abs_zero]
    exact mul_nonneg (by positivity) dist_nonneg
  · rintro r ⟨f,hf,rfl⟩
    rw [←hfst,←hsnd,
      integral_map measurable_fst.aemeasurable (lip_continuous f hf).aestronglyMeasurable,
      integral_map measurable_snd.aemeasurable (lip_continuous f hf).aestronglyMeasurable,
      hint,hint]
    calc
      _=∑ i, ∑ j, wt i j*(f (eigenAngle (z i))-f (eigenAngle (w j))) := by
        simp only [mul_sub,Finset.sum_sub_distrib]
      _≤Real.pi/2*mean := by
        dsimp [mean]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have ht := (le_abs_self _).trans ((hf (eigenAngle (z i)) (eigenAngle (w j))).trans
          (arcDist_le_chord (eigenAngle (z i)) (eigenAngle (w j))))
        rw [hzphase,hwphase] at ht
        have hh := mul_le_mul_of_nonneg_left ht (hw0 i j)
        nlinarith only [hh]
      _≤_ := mul_le_mul_of_nonneg_left hmean (by positivity)

theorem rotate_state {d : Nat} (U : Mat d) (hU : IsUnitary U) (s t : State d)
    (ht : t.rho=U.conjTranspose*s.rho*U) (Y : Mat d) (hY : IsUnitary Y) :
    W1 (spectralMeasure Y hY t) (spectralMeasure Y hY s)≤Real.pi*hs (comm U s.xi) := by
  let V := (spectralData Y hY).1
  let z := (spectralData Y hY).2
  have hp := spectralData_properties Y hY
  let B := s.xi*U*V
  let C := U*s.xi*V
  have hB : B.conjTranspose*B=V.conjTranspose*t.rho*V := by
    simp only [B,Matrix.conjTranspose_mul,s.xi_positive.isHermitian.eq]
    rw [ht]
    calc
      _=V.conjTranspose*U.conjTranspose*(s.xi*s.xi)*U*V := by simp only [Matrix.mul_assoc]
      _=_ := by rw [s.xi_square]; simp only [Matrix.mul_assoc]
  have hC : C.conjTranspose*C=V.conjTranspose*s.rho*V := by
    simp only [C,Matrix.conjTranspose_mul,s.xi_positive.isHermitian.eq]
    calc
      _=V.conjTranspose*s.xi*(U.conjTranspose*U)*s.xi*V := by simp only [Matrix.mul_assoc]
      _=V.conjTranspose*(s.xi*s.xi)*V := by rw [hU.1,Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _=_ := by rw [s.xi_square]
  have hnorm : hs s.xi=1 := by
    have hn : hsNorm s.xi^2=1 := by
      rw [hsNorm_sq,hsSquared_trace,s.xi_positive.isHermitian.eq,s.xi_square,s.normalized]
      rfl
    change hsNorm s.xi=1
    nlinarith [hsNorm_nonneg s.xi]
  have hnB : hs B=1 := by
    change hsNorm (s.xi*U*V)=1
    rw [hsNorm_unitary_right V _ hp.1.2,hsNorm_unitary_right U _ hU.2]
    exact hnorm
  have hnC : hs C=1 := by
    change hsNorm (U*s.xi*V)=1
    rw [hsNorm_unitary_right V _ hp.1.2,hsNorm_unitary_left U _ hU.1]
    exact hnorm
  have hnD : hs (B-C)=hs (comm U s.xi) := by
    have he : B-C=-(comm U s.xi)*V := by
      simp only [B,C,Companion.Analytic.comm,Matrix.sub_mul,Matrix.neg_mul]
      module
    have hneg : hsNorm (-(comm U s.xi))=hsNorm (comm U s.xi) := by
      simp only [hsNorm,hsSquared,Matrix.neg_apply,Complex.normSq_neg]
    rw [he,hs_eq_hsNorm,hsNorm_unitary_right V _ hp.1.2,hneg]
    rfl
  have hmoment (f : Torus → ℝ) :
      (∫ x, f x ∂spectralMeasure Y hY t)-(∫ x, f x ∂spectralMeasure Y hY s)=
        ∑ i, ∑ j, f (eigenAngle (z j))*(Complex.normSq (B i j)-Complex.normSq (C i j)) := by
    rw [spectralMeasure_eq_resolution Y V hY z t hp.1 hp.2.2,
      spectralMeasure_eq_resolution Y V hY z s hp.1 hp.2.2,
      resolutionMeasure_integral,resolutionMeasure_integral,←hB,←hC]
    simp_rw [←W2.col_normSq]
    rw [←Finset.sum_sub_distrib]
    simp_rw [←sub_mul,←Finset.sum_sub_distrib,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply csSup_le
  · refine ⟨0,fun _ => 0,?_,by simp⟩
    intro x y
    simp only [sub_self,abs_zero]
    exact mul_nonneg (by positivity) dist_nonneg
  · rintro r ⟨f,hf,rfl⟩
    obtain ⟨c,hc⟩ := lip_center f hf
    let g : Torus → ℝ := fun x => f x-c
    have hsub :
        (∫ x, f x ∂spectralMeasure Y hY t)-(∫ x, f x ∂spectralMeasure Y hY s)=
        (∫ x, g x ∂spectralMeasure Y hY t)-(∫ x, g x ∂spectralMeasure Y hY s) := by
      letI := spectral_probability Y hY t
      letI := spectral_probability Y hY s
      simp only [g,integral_sub (lip_integrable f hf _) (integrable_const c),integral_const,
        probReal_univ,one_smul]
      ring
    rw [hsub,hmoment]
    have hb := W2.weighted_normSq_difference B C (fun j => g (eigenAngle (z j))) (Real.pi/2)
      (by positivity) (fun j => hc _)
    rw [hnB,hnC,hnD] at hb
    exact (le_abs_self _).trans (hb.trans_eq (by ring))

end
end Blueprint.FCircle
