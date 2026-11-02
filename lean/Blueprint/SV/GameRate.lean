import Blueprint.Definitions

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped ENNReal

/-- A family of models in dimension 16m with errors A/m gives value one and
the required inverse-square-root game-dimension upper rate. -/
theorem game_rate_of_models (g : LCS) (A : ℝ) (hA : 0<A)
    (hmodels : ∀ m : Nat, 0<m → ∃ U : Nat → Mat (16*m),
      (∀ j, IsUnitary (U j)) ∧
      (∀ k r, relator g.system k=some r → normalizedHS (wordEval U r-1)≤A/m) ∧
      U (g.system.n+1)=-1) :
    quantumValueOne g ∧ ∃ C : ℝ, 0<C ∧ ∀ e, 0<e → e≤1 →
      gameDimensionProfile g e≤ENNReal.ofReal (C/Real.sqrt e) := by
  let R := returnConstant g.arity
  have hR : 0<R := ReturnProof.returnConstant_pos (ProfileProof.arity_pos g)
  let q := A*Real.sqrt R
  have hq : 0<q := mul_pos hA (Real.sqrt_pos.mpr hR)
  let C := 16*(q+1)
  have hC : 0<C := by dsimp [C]; positivity
  have strategies (e : ℝ) (he : 0<e) (he1 : e≤1) :
      ∃ d : Nat, ∃ s : Strategy g d d, 1-e≤win s ∧ (d:ℝ)≤C/Real.sqrt e := by
    have hs : 0<Real.sqrt e := Real.sqrt_pos.mpr he
    let m := ⌈q/Real.sqrt e⌉₊
    have hmR : (0:ℝ)<m := (div_pos hq hs).trans_le (Nat.le_ceil _)
    have hm : 0<m := by exact_mod_cast hmR
    obtain ⟨U,hU,hrel,hJ⟩ := hmodels m hm
    have herror : R*(A/(m:ℝ))^2≤e := by
      have hceil : q≤(m:ℝ)*Real.sqrt e := (div_le_iff₀ hs).mp (Nat.le_ceil _)
      have hsq := pow_le_pow_left₀ hq.le hceil 2
      dsimp only [q] at hsq
      simp only [mul_pow,Real.sq_sqrt he.le,Real.sq_sqrt hR.le] at hsq
      have hid : R*(A/(m:ℝ))^2=(A^2*R)/(m:ℝ)^2 := by ring
      rw [hid]
      exact (div_le_iff₀ (sq_pos_of_pos hmR)).mpr (by nlinarith only [hsq])
    obtain ⟨s,_,_,_,hwin⟩ := MainProof.flat_return_strategy g (16*m) (by omega) U hU
      (A/(m:ℝ)) (by positivity) hrel hJ
    refine ⟨16*m,s,(by linarith : 1-e≤1-R*(A/(m:ℝ))^2).trans hwin,?_⟩
    apply (le_div_iff₀ hs).mpr
    have hceil : (m:ℝ)≤q/Real.sqrt e+1 := (Nat.ceil_lt_add_one (div_nonneg hq.le hs.le)).le
    have hmul := mul_le_mul_of_nonneg_right hceil hs.le
    have hid : (q/Real.sqrt e+1)*Real.sqrt e=q+Real.sqrt e := by field_simp
    rw [hid] at hmul
    have hs1 : Real.sqrt e≤1 := by nlinarith [Real.sq_sqrt he.le,Real.sqrt_nonneg e]
    dsimp [C]
    push_cast
    nlinarith only [hmul,hs1]
  constructor
  · intro e he
    obtain ⟨d,s,hw,_⟩ := strategies (min e 1) (lt_min he (by norm_num)) (min_le_right _ _)
    exact ⟨d,s,(by linarith [min_le_left e 1] : 1-e≤1-min e 1).trans hw⟩
  · refine ⟨C,hC,?_⟩
    intro e he he1
    obtain ⟨d,s,hw,hd⟩ := strategies e he he1
    calc
      _ ≤ (d:ℝ≥0∞) := by unfold gameDimensionProfile; exact sInf_le ⟨d,s,hw,rfl⟩
      _ ≤ _ := by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hd

end
end Blueprint.SV

#print axioms Blueprint.SV.game_rate_of_models
