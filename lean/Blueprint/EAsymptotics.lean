import Blueprint.ERates
import Blueprint.MixedStates
import Blueprint.W2.PureStates

namespace Blueprint.EAsymptotics
noncomputable section
open Companion Companion.Analytic
set_option maxHeartbeats 600000

def formationProfile (n : Nat) (eps : ℝ) : ℝ := sInf {v | ∃ (a b : Nat)
  (sigma : QIT.State (Fin a × Fin b)) (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b),
  (∀ i, contraction (A i)) ∧ (∀ i j, i≠j → contraction (B i j)) ∧
  (1-eps)*optimalBias≤mixedCHSHBias sigma A B ∧ v=entanglementFormation sigma}

def ThetaRate (f : Nat → ℝ → ℝ) : Prop := ∃ c C R : ℝ, 0<c ∧ 0<C ∧ 0<R ∧
  ∀ (n : Nat) (eps : ℝ), 3≤n → 0<eps → eps≤1 → R≤min (n:ℝ) (1/eps) →
    c*min (n:ℝ) (1/eps)≤f n eps ∧ f n eps≤C*min (n:ℝ) (1/eps)

theorem theta (hP : EProfiles) (hM : EMixed) :
    ThetaRate chshEntropyProfile ∧ ThetaRate formationProfile := by
  have hu (n : Nat) (eps : ℝ) (he : 0<eps) (he1 : eps≤1) :
      min ((n/2:Nat):ℝ) (⌈1/eps⌉₊:ℝ)≤2*min (n:ℝ) (1/eps) := by
    have hn : ((n/2:Nat):ℝ)≤n := by exact_mod_cast Nat.div_le_self n 2
    have hceil := (Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤1/eps)).le
    have hinv : (1:ℝ)≤1/eps := (le_div_iff₀ he).mpr (by linarith)
    by_cases h : (n:ℝ)≤1/eps
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right (le_of_not_ge h)]
      exact (min_le_right _ _).trans (by linarith)
  have hmLower (n : Nat) (eps : ℝ) (hn : 3≤n) (he : 0<eps) :
      (chshM n (2*eps):ℝ)/4≤formationProfile n eps := by
    apply le_csInf
    · obtain ⟨a,b,psi,A,B,hv,hw,_⟩ := ERates.approximate_upper n eps (by omega) he
      let sigma := W2.pureState psi hv.1
      have hmix : mixedCHSHBias sigma A B=chshBias psi A B := by
        simpa using MixedStates.mixed_chsh_linear sigma (fun _ : Fin 1 => (1:ℝ))
          (fun _ => psi) (W2.pureState_decomposition psi hv.1) A B
      exact ⟨_,a,b,sigma,A,B,hv.2.1,hv.2.2,hmix.symm ▸ hw,rfl⟩
    · rintro v ⟨a,b,sigma,A,B,hA,hB,hw,rfl⟩
      exact hM n a b sigma A B eps hn he hA hB hw
  have hmUpper (n : Nat) (eps : ℝ) (hn : 3≤n) (he : 0<eps) :
      formationProfile n eps≤min ((n/2:Nat):ℝ) (⌈1/eps⌉₊:ℝ) := by
    have hbound : BddBelow {v | ∃ (a b : Nat) (sigma : QIT.State (Fin a × Fin b))
        (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b),
        (∀ i, contraction (A i)) ∧ (∀ i j, i≠j → contraction (B i j)) ∧
        (1-eps)*optimalBias≤mixedCHSHBias sigma A B ∧ v=entanglementFormation sigma} := by
      refine ⟨(chshM n (2*eps):ℝ)/4,?_⟩
      rintro v ⟨a,b,sigma,A,B,hA,hB,hw,rfl⟩
      exact hM n a b sigma A B eps hn he hA hB hw
    have hpure (a b : Nat) (psi : Matrix (Fin b) (Fin a) ℂ) A B
        (hv : validCHSH (n:=n) psi A B) (hw : (1-eps)*optimalBias≤chshBias psi A B) :
        formationProfile n eps≤entropy (psi.conjTranspose*psi) := by
      let sigma := W2.pureState psi hv.1
      have hmix : mixedCHSHBias sigma A B=chshBias psi A B := by
        simpa using MixedStates.mixed_chsh_linear sigma (fun _ : Fin 1 => (1:ℝ))
          (fun _ => psi) (W2.pureState_decomposition psi hv.1) A B
      have hformation := MixedStates.formation_pure psi hv.1 sigma rfl
      exact csInf_le hbound ⟨a,b,sigma,A,B,hv.2.1,hv.2.2,hmix.symm ▸ hw,hformation.symm⟩
    obtain ⟨psi,A,B,hv,hw,hent⟩ := ERates.exact_upper n (by omega)
    have hw' : (1-eps)*optimalBias≤chshBias psi A B := by
      rw [hw]
      have hb : 0≤optimalBias := by unfold optimalBias; positivity
      nlinarith
    obtain ⟨a,b,psi',A',B',hv',hw'',hent'⟩ := ERates.approximate_upper n eps (by omega) he
    exact le_min ((hpure _ _ psi A B hv hw').trans hent)
      ((hpure a b psi' A' B' hv' hw'').trans hent')
  constructor
  · refine ⟨1/480000000,2,120000000,by norm_num,by norm_num,by norm_num,?_⟩
    intro n eps hn he he1 hR
    have hp := hP n eps hn he he1
    exact ⟨by linarith [hp.1],hp.2.trans (hu n eps he he1)⟩
  · refine ⟨1/480000000,2,120000000,by norm_num,by norm_num,by norm_num,?_⟩
    intro n eps hn he he1 hR
    refine ⟨?_,(hmUpper n eps hn he).trans (hu n eps he he1)⟩
    have ht0 : 0≤min (n:ℝ) (1/eps) := le_min (Nat.cast_nonneg _) (by positivity)
    have htN := min_le_left (n:ℝ) (1/eps)
    have htE := min_le_right (n:ℝ) (1/eps)
    have hscaled : min (n:ℝ) (1/eps)/20000000≤
        min (n:ℝ) ((1/10000000:ℝ)/(2*eps)) := by
      apply le_min
      · nlinarith
      · have heq : (1/10000000:ℝ)/(2*eps)=(1/eps)/20000000 := by ring
        rw [heq]
        exact div_le_div_of_nonneg_right htE (by norm_num)
    have hf := Nat.sub_one_lt_floor
      (min (n:ℝ) ((1/10000000:ℝ)/(2*eps))/3)
    change min (n:ℝ) ((1/10000000:ℝ)/(2*eps))/3-1<(chshM n (2*eps):ℝ) at hf
    have hb := hmLower n eps hn he
    linarith

end
end Blueprint.EAsymptotics
