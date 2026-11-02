import Blueprint.FCircle
import Blueprint.AWordArea
import Blueprint.W2.KInvariance
import Blueprint.W2.KNormalized
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Blueprint.W2.EvenRepresentation
import Blueprint.SV.FlatSector

namespace Blueprint.FProfile
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ENNReal
set_option maxHeartbeats 600000

theorem near_invariance {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (he : 0<e) (hm : kModel U s e) :
    ∃ hY : IsUnitary (U 5),
      FCircle.W1 (MeasureTheory.Measure.map FCircle.doubling (FCircle.spectralMeasure (U 5) hY s))
        (FCircle.spectralMeasure (U 5) hY s)≤5*Real.pi*e ∧
      FCircle.W1 (MeasureTheory.Measure.map FCircle.halfTurn (FCircle.spectralMeasure (U 5) hY s))
        (FCircle.spectralMeasure (U 5) hY s)≤19/2*Real.pi*e := by
  let V := W2.kAssignment U
  have hV (j : Nat) : IsUnitary (V j) := by
    dsimp [V,W2.kAssignment]
    split
    · exact hm.1 j
    · simp [IsUnitary]
  have hc (j : Nat) : hs (comm (V j) s.xi)≤e := by
    by_cases hj : 1≤j ∧ j≤5
    · simpa only [V,W2.kAssignment,ite_eq_left hj] using hm.2.2.1 j hj.1 hj.2
    · simp only [V,W2.kAssignment,ite_eq_right hj]
      simpa [Companion.Analytic.comm,hs] using he.le
  have hr (r : Word) (hmem : r∈kRelators) : hs ((wordEval V r-1)*s.xi)≤e := by
    rw [show wordEval V r=wordEval U r from W2.kAssignment_relators U r hmem]
    exact hm.2.1 r hmem
  have hvisible : hs ((V 3+1)*s.xi)≤e := by
    simpa [V,W2.kAssignment] using hm.2.2.2
  have hb := W2.k_near_global V s e hV hr hc hvisible
  refine ⟨hm.1 5,?_,?_⟩
  · simpa [V,W2.kAssignment] using hb.1
  · simpa [V,W2.kAssignment] using hb.2

theorem state_dimension {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (he : 0<e) (hm : kModel U s e) : 1/(29*e)≤(d:ℝ) := by
  obtain ⟨hY,hdouble,hhalf⟩ := near_invariance U s e he hm
  let mu := FCircle.spectralMeasure (U 5) hY s
  have hp := FCircle.spectral_probability (U 5) hY s
  obtain ⟨S,hcard,hzero⟩ := FCircle.spectral_support (U 5) hY s
  have hd : 0<d := by
    by_contra hh
    have hd0 : d=0 := by omega
    subst d
    have hh := s.normalized
    simp [Matrix.trace] at hh
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hbot := FCircle.atomic_obstruction d hd mu hp S hcard hzero
  have htop := FCircle.haar_comparison mu hp
  have hineq : Real.pi/(2*d)≤(29/2:ℝ)*Real.pi*e := by
    exact hbot.trans (htop.trans (by dsimp [mu] at *; linarith))
  have hz := (div_le_iff₀ (by positivity : (0:ℝ)<2*d)).mp hineq
  have hz' : Real.pi*1≤Real.pi*(29*e*d) := by nlinarith
  have hone : (1:ℝ)≤29*e*d := (mul_le_mul_iff_right₀ Real.pi_pos).mp hz'
  exact (div_le_iff₀ (by positivity : (0:ℝ)<29*e)).mpr (by nlinarith)

def evenY (m : Nat) : Mat (2*m) := Matrix.diagonal (fun j =>
  Complex.exp (((2*Real.pi*j.val/(2*m):ℝ):ℂ)*Complex.I))
def evenA (m : Nat) : Mat (2*m) := fun i j => if (j.val+m)%(2*m)=i.val then 1 else 0
def evenX (m : Nat) : Mat (2*m) := fun i j =>
  if 2*(i.val%m)+i.val/m=j.val then 1 else 0
def evenAssignment (m : Nat) : Nat → Mat (2*m)
  | 1 => evenA m | 2 => -(evenA m) | 3 => -1 | 4 => evenX m | 5 => evenY m | _ => 1

theorem even_model (m : Nat) (hm : 0<m) :
    (∀ j, IsUnitary (evenAssignment m j)) ∧
      normalizedHS (wordEval (evenAssignment m) kRelators[0]-1)=Real.sqrt 2*Real.sin (Real.pi/(2*m)) ∧
      ∀ r∈kRelators.drop 1, wordEval (evenAssignment m) r=1 := by
  have hY : evenY m=W2.evenClock m := by
    apply congrArg Matrix.diagonal
    funext j
    exact (W2.evenPhase_formula m hm j.val).symm
  have hA : evenA m=(W2.halfSwap m hm).permMatrix ℂ := by
    ext i j
    have hcond : (j.val+m)%(2*m)=i.val ↔ (W2.halfSwap m hm) i=j := by
      rw [←W2.halfSwap_val m hm j]
      constructor
      · intro h
        have hh : (W2.halfSwap m hm) j=i := Fin.ext h
        have hc := congrArg (W2.halfSwap m hm) hh
        have hi : (W2.halfSwap m hm) ((W2.halfSwap m hm) j)=j := (W2.halfSwap m hm).left_inv j
        rw [hi] at hc
        exact hc.symm
      · intro h
        rw [←h]
        exact congrArg Fin.val ((W2.halfSwap m hm).left_inv i)
    simp only [evenA,Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_apply,Pi.single_apply]
    simp [hcond,eq_comm]
  have hX : evenX m=(W2.shuffle m hm).permMatrix ℂ := by
    ext i j
    have hcond : 2*(i.val%m)+i.val/m=j.val ↔ (W2.shuffle m hm) i=j := by
      rw [←W2.shuffle_val m hm i]
      exact Fin.ext_iff.symm
    simp only [evenX,Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_apply,Pi.single_apply]
    simp [hcond,eq_comm]
  have hU : evenAssignment m=W2.evenRepresentation m hm := by
    funext j
    unfold evenAssignment W2.evenRepresentation
    split <;> simp only [hA,hX,hY]
  rw [hU]
  exact ⟨W2.evenRepresentation_unitary m hm,W2.evenRepresentation_first m hm,
    W2.evenRepresentation_exact m hm⟩

/-- SV18 Proposition 2.7, central-involution separation amplification. -/
theorem even_upper (e : ℝ) (he : 0<e) :
    kHyperlinearProfile 2 e≤(2*⌈Real.pi/(Real.sqrt 2*e)⌉₊:Nat) := by
  let m := ⌈Real.pi/(Real.sqrt 2*e)⌉₊
  have hmR : (0:ℝ)<m := (by positivity : (0:ℝ)<Real.pi/(Real.sqrt 2*e)).trans_le (Nat.le_ceil _)
  have hm : 0<m := by exact_mod_cast hmR
  obtain ⟨hU,herr,hexact⟩ := even_model m hm
  have hbound : Real.sqrt 2*Real.sin (Real.pi/(2*m))≤e := by
    have hceil := (div_le_iff₀ (by positivity : (0:ℝ)<Real.sqrt 2*e)).mp
      (show Real.pi/(Real.sqrt 2*e)≤(m:ℝ) from Nat.le_ceil _)
    have hscale := mul_le_mul_of_nonneg_left hceil (Real.sqrt_nonneg (2:ℝ))
    have hr : Real.sqrt 2*Real.pi≤2*(e*m) := by
      calc
        _≤Real.sqrt 2*((m:ℝ)*(Real.sqrt 2*e)) := hscale
        _=(Real.sqrt 2)^2*(e*m) := by ring
        _=2*(e*m) := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    calc
      _≤Real.sqrt 2*(Real.pi/(2*m)) := mul_le_mul_of_nonneg_left (Real.sin_le (by positivity)) (Real.sqrt_nonneg _)
      _≤e := by
        rw [←mul_div_assoc]
        exact (div_le_iff₀ (by positivity : (0:ℝ)<2*m)).mpr (by nlinarith only [hr])
  have hrep : normalizedRepresentation kRelators (evenAssignment m) e := by
    refine ⟨hU,?_⟩
    intro r hmem
    have hdecomp : kRelators=kRelators[0]::kRelators.drop 1 := rfl
    rw [hdecomp] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact herr.le.trans hbound
    · rw [hexact r hmem,sub_self]
      simpa only [normalizedHS,hsNorm,hsSquared,Matrix.zero_apply,Complex.normSq_zero,
        Finset.sum_const_zero,Real.sqrt_zero,mul_zero] using he.le
  apply sInf_le
  refine ⟨2*m,evenAssignment m,by omega,hrep,?_,rfl⟩
  have hJ : evenAssignment m 3=-1 := rfl
  rw [hJ,W2.normalized_minus_identity (2*m) (by omega)]

theorem large_error_profile (e : ℝ) (he : 2≤e) : kHyperlinearProfile 2 e≤1 := by
  let U : Nat → Mat 1 := fun j => if j=3 then -1 else 1
  have hU : ∀ j, IsUnitary (U j) := by
    intro j
    dsimp [U]
    split <;> simp [IsUnitary]
  have hr : normalizedRepresentation kRelators U e := by
    refine ⟨hU,?_⟩
    intro r hmem
    simp only [kRelators,List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [wordEval,U,normalizedHS,hsNorm,hsSquared] <;> linarith
  unfold kHyperlinearProfile
  apply sInf_le
  refine ⟨1,U,by decide,hr,?_,by simp⟩
  change 2≤normalizedHS (-1-1:Mat 1)
  rw [W2.normalized_minus_identity 1 (by decide)]

theorem separation_amplification (delta : ℝ) (hd : 0<delta) (hd2 : delta≤2) :
    ∃ C : ℝ, 1≤C ∧ ∀ e : ℝ, 0<e →
      kHyperlinearProfile 2 (C*e)≤kHyperlinearProfile delta e := by
  obtain ⟨K,hK,hcentral⟩ := SV.k_central_constant
  let H := 116*(K+2)/delta
  have hH : 0<H := by dsimp [H]; positivity
  have hHd : H*delta=116*(K+2) := by dsimp [H]; field_simp
  have hH1 : 1≤H := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  let C := 100*(Real.pi+1)*H
  have hC : 0<C := by dsimp [C]; positivity
  have hC1 : 1≤C := by dsimp [C]; nlinarith [Real.pi_pos]
  have hC8 : 8*H≤C := by dsimp [C]; nlinarith [Real.pi_pos]
  have hCd : 4≤C*delta := by
    have hh := mul_le_mul_of_nonneg_right hC8 hd.le
    nlinarith
  have hCp : 4*Real.pi*H≤C := by dsimp [C]; nlinarith [Real.pi_pos]
  refine ⟨C,hC1,?_⟩
  intro e he
  change kHyperlinearProfile 2 (C*e)≤sInf {v | ∃ d U,
    0<d ∧ normalizedRepresentation (d:=d) kRelators U e ∧ delta≤normalizedHS (U 3-1) ∧ v=(d:ℝ≥0∞)}
  apply le_sInf
  rintro v ⟨d,U,hdim,hrep,hsep,rfl⟩
  have hCe : 0<C*e := mul_pos hC he
  by_cases hlarge : 2≤C*e
  · exact (large_error_profile (C*e) hlarge).trans (by exact_mod_cast hdim)
  have hsmall : C*e<2 := lt_of_not_ge hlarge
  have hesmall : e≤delta/2 := by
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith
  obtain ⟨t,ht⟩ := SV.flat_visible_sector K hK hcentral d hdim U e delta he hd hesmall hrep hsep
  have hprec : 0<4*(K+2)*e/delta := by positivity
  have hdimLower : 1/(H*e)≤(d:ℝ) := by
    have hh := state_dimension U t (4*(K+2)*e/delta) hprec ht
    convert hh using 1
    dsimp [H]
    congr 1
    ring
  have hHe : 0<H*e := mul_pos hH he
  have hsmallH : H*e<1/4 := by
    have hh := mul_le_mul_of_nonneg_right hC8 he.le
    nlinarith
  have hfour : (4:ℝ)≤d := by
    have hinv : (4:ℝ)<1/(H*e) := (lt_div_iff₀ hHe).mpr (by nlinarith)
    exact (hinv.trans_le hdimLower).le
  let m := ⌈Real.pi/(Real.sqrt 2*(C*e))⌉₊
  have hceil : (m:ℝ)≤Real.pi/(Real.sqrt 2*(C*e))+1 :=
    (Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤Real.pi/(Real.sqrt 2*(C*e)))).le
  have hsqrt : 1≤Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hratio : Real.pi/(Real.sqrt 2*(C*e))≤Real.pi/(C*e) :=
    div_le_div_of_nonneg_left Real.pi_pos.le hCe (by nlinarith)
  have hcoef : 2*Real.pi*H/C≤1/2 := (div_le_iff₀ hC).mpr (by nlinarith)
  have hfrac : 2*Real.pi/(C*e)=(2*Real.pi*H/C)*(1/(H*e)) := by
    field_simp
  have hnum : (2*m:Nat)≤d := by
    have hreal : ((2*m:Nat):ℝ)≤d := by
      push_cast
      have h1 : 2*(m:ℝ)≤2*Real.pi/(C*e)+2 := by
        calc
          _ ≤ 2*(Real.pi/(Real.sqrt 2*(C*e))+1) := mul_le_mul_of_nonneg_left hceil (by norm_num)
          _ ≤ 2*(Real.pi/(C*e)+1) := mul_le_mul_of_nonneg_left (add_le_add hratio le_rfl) (by norm_num)
          _ = _ := by ring
      have h2 : 2*Real.pi/(C*e)≤(1/(H*e))/2 := by
        rw [hfrac]
        have hh := mul_le_mul_of_nonneg_right hcoef (by positivity : (0:ℝ)≤1/(H*e))
        nlinarith
      linarith
    exact_mod_cast hreal
  exact (even_upper (C*e) hCe).trans (by exact_mod_cast hnum)

theorem profiles : KProfile := by
  have lowerState (e : ℝ) (he : 0<e) : ENNReal.ofReal (1/(29*e))≤kStateProfile e := by
    unfold kStateProfile
    apply le_sInf
    rintro v ⟨d,U,s,hm,rfl⟩
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (state_dimension U s e he hm)
  have flatComparison (e : ℝ) (he : 0<e) : kStateProfile e≤kHyperlinearProfile 2 e := by
    unfold kHyperlinearProfile
    apply le_sInf
    rintro v ⟨d,U,hd,hr,hsep,rfl⟩
    have hJ := W2.maximal_unitary_separation hd (U 3) (hr.1 3) hsep
    exact sInf_le ⟨d,U,MainProof.flatState d hd,W2.flat_kModel hd U e he.le hr hJ,rfl⟩
  have evenUpper := even_upper
  refine ⟨fun e he => ⟨lowerState e he,flatComparison e he,evenUpper e he⟩,?_⟩
  intro delta hd hd2
  obtain ⟨C,hC,hsep⟩ := separation_amplification delta hd hd2
  refine ⟨1/(29*C),Real.sqrt 2*Real.pi+4,by positivity,by positivity,?_⟩
  intro e he he2
  constructor
  · have hC0 : 0<C := by linarith
    calc
      _=ENNReal.ofReal (1/(29*(C*e))) := by congr 1; ring
      _≤kStateProfile (C*e) := lowerState _ (by positivity)
      _≤kHyperlinearProfile 2 (C*e) := flatComparison _ (by positivity)
      _≤kHyperlinearProfile delta e := hsep e he
  · have hc := (Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤Real.pi/(Real.sqrt 2*e))).le
    have hupper : (2*⌈Real.pi/(Real.sqrt 2*e)⌉₊:Nat)≤ENNReal.ofReal ((Real.sqrt 2*Real.pi+4)/e) := by
      have hreal : ((2*⌈Real.pi/(Real.sqrt 2*e)⌉₊:Nat):ℝ)≤(Real.sqrt 2*Real.pi+4)/e := by
        apply (le_div_iff₀ he).mpr
        have hc' := mul_le_mul_of_nonneg_right hc he.le
        have hident : Real.pi/(Real.sqrt 2*e)*e=Real.sqrt 2*Real.pi/2 := by
          have hs : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
          field_simp
          <;> nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
        rw [add_mul,hident,one_mul] at hc'
        push_cast
        nlinarith only [hc',he2]
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal
    exact (W2.kHyperlinearProfile_mono_delta delta hd2 e).trans ((evenUpper e he).trans hupper)

end
end Blueprint.FProfile

#print axioms Blueprint.FProfile.even_upper
#print axioms Blueprint.FProfile.large_error_profile
#print axioms Blueprint.FProfile.separation_amplification
