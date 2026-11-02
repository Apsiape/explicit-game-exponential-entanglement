import Blueprint.A.AreaCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Blueprint.PairProof
open Companion
open scoped BigOperators

theorem pair_numeric_bound (N L : Nat) (hN : 1≤N)
    (hL : (L:ℝ)≤10*(2:ℝ)^((log2 (1500*(max 3 N:Nat))+6)^2)+700*(max 3 N:Nat)) :
    ((100*N^3*L:Nat):ℝ)≤(2:ℝ)^((log2 N+23)^2) := by
  let x := log2 N
  let Q : ℝ := (2:ℝ)^((x+19)^2)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hln : 0≤x := div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (Real.log_pos (by norm_num)).le
  have hmax : max 3 N≤3*N := by omega
  have hmaxR : ((max 3 N:Nat):ℝ)≤3*N := by exact_mod_cast hmax
  have hpos : (0:ℝ)<1500*(max 3 N:Nat) := by positivity
  have harg : (1500:ℝ)*(max 3 N:Nat)≤(2:ℝ)^13*N := by
    calc
      _ ≤ 1500*(3*(N:ℝ)) := mul_le_mul_of_nonneg_left hmaxR (by norm_num)
      _ ≤ _ := by norm_num; nlinarith
  have hlog : log2 (1500*(max 3 N:Nat))≤x+13 := by
    have hh := Real.log_le_log hpos harg
    rw [Real.log_mul (by norm_num : (2:ℝ)^13≠0) hn.ne',Real.log_pow] at hh
    dsimp [log2,x]
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    convert hh using 1 <;> field_simp <;> ring
  have hlog0 : 0≤log2 (1500*(max 3 N:Nat)) := by
    apply div_nonneg _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    apply Real.log_nonneg
    have : (3:Nat)≤max 3 N := le_max_left _ _
    have : (3:ℝ)≤(max 3 N:Nat) := by exact_mod_cast this
    nlinarith
  have hpow : (2:ℝ)^((log2 (1500*(max 3 N:Nat))+6)^2)≤Q := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)
  have hNx : (2:ℝ)^x=N := Real.rpow_logb (by norm_num) (by norm_num) hn
  have hNQ : (N:ℝ)≤Q := by
    rw [←hNx]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hLQ : (L:ℝ)≤2110*Q := by nlinarith
  have hstep : ((100*N^3*L:Nat):ℝ)≤(2:ℝ)^18*(N:ℝ)^3*Q := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left hLQ (by positivity : (0:ℝ)≤100*(N:ℝ)^3)
    have hQ0 : 0≤Q := by positivity
    calc
      _ ≤ 100*(N:ℝ)^3*(2110*Q) := hh
      _ ≤ _ := by
        have hp : (0:ℝ)≤(N:ℝ)^3*Q := mul_nonneg (by positivity) hQ0
        norm_num
        nlinarith only [hp]
  have h3 : (2:ℝ)^(3*x)=(N:ℝ)^3 := by
    rw [show 3*x=x*3 by ring,Real.rpow_mul (by norm_num : (0:ℝ)≤2),hNx]
    norm_num
  have hexp : (2:ℝ)^18*(N:ℝ)^3*Q=(2:ℝ)^(18+3*x+(x+19)^2) := by
    rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num),h3]
    norm_num [Q]
  have htop : (2:ℝ)^(18+3*x+(x+19)^2)≤(2:ℝ)^((x+23)^2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  exact hstep.trans (by rw [hexp]; exact htop)

end Blueprint.PairProof

#print axioms Blueprint.PairProof.pair_numeric_bound
