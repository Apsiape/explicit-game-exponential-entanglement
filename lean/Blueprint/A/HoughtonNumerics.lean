import Blueprint.A.HoughtonUniform
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem log2_six_le : log2 (6:ℝ)≤13/5 := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<6^5) (by norm_num : (6:ℝ)^5≤2^13)
  rw [Real.log_pow,Real.log_pow] at h
  unfold log2
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  norm_num at h ⊢
  linarith

theorem log2_thirtysix_le : log2 (36:ℝ)≤26/5 := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<36^5) (by norm_num : (36:ℝ)^5≤2^26)
  rw [Real.log_pow,Real.log_pow] at h
  unfold log2
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  norm_num at h ⊢
  linarith

theorem collection_clog_minus_one (n : Nat) (hn : 1≤n) :
    ((Nat.clog 2 (4*n+2)-1:Nat):ℝ)≤log2 n+13/5 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hp : (2:Nat)^(Nat.clog 2 (4*n+2)-1)<4*n+2 := by
    simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<4*n+2)
  have hb : (2:ℝ)^(Nat.clog 2 (4*n+2)-1)≤6*(n:ℝ) := by
    exact_mod_cast (show (2:Nat)^(Nat.clog 2 (4*n+2)-1)≤6*n by omega)
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.clog 2 (4*n+2)-1)) hb
  rw [Real.log_pow,Real.log_mul (by norm_num : (6:ℝ)≠0) hnR.ne'] at hlog
  have h6 : Real.log 6≤(13/5:ℝ)*Real.log 2 := (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp log2_six_le
  have he : Real.log (n:ℝ)=log2 n*Real.log 2 := by unfold log2; field_simp
  apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp
  rw [he] at hlog
  nlinarith

theorem collection_clog_power (n : Nat) (hn : 1≤n) :
    (2:Nat)^Nat.clog 2 (4*n+2)≤12*n := by
  have hpos := clog_two_pos (4*n+2) (by omega)
  have hp : (2:Nat)^(Nat.clog 2 (4*n+2)-1)<4*n+2 := by
    simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<4*n+2)
  rw [show Nat.clog 2 (4*n+2)=(Nat.clog 2 (4*n+2)-1)+1 by omega,pow_succ]
  omega

theorem uniformFarCap_collection_bound (n : Nat) (hn : 1≤n) :
    uniformFarCap (4*n+2)+1≤5*(36*n)^(Nat.clog 2 (4*n+2)-1) := by
  let t := Nat.clog 2 (4*n+2)-1
  have hp := clog_two_pos (4*n+2) (by omega)
  have he : t+1=Nat.clog 2 (4*n+2) := by dsimp [t]; omega
  have hcap := dyadicCap_ge_five t
  have hD : dyadicCap t=5*(3*2^(t+1))^t := by
    simp only [dyadicCap,mul_pow,←pow_mul,Nat.mul_comm t (t+1)]
    ring
  have hb : 3*2^(t+1)≤36*n := by rw [he]; have hh := collection_clog_power n hn; omega
  have ht : (3*2^(t+1))^t≤(36*n)^t := Nat.pow_le_pow_left hb t
  have hsmall : uniformFarCap (4*n+2)+1≤dyadicCap t := by dsimp [uniformFarCap,t] at *; omega
  rw [hD] at hsmall
  dsimp [t] at ht
  exact hsmall.trans (Nat.mul_le_mul_left 5 ht)

/-- The original explicit Corollary A.5 bound, after charging the complete
collection cost. All rounding and small-n cases are included. -/
theorem collection_numeric_bound (n : Nat) (hn : 1≤n) :
    ((400*n^4*(uniformFarCap (4*n+2)+1):Nat):ℝ)≤(2:ℝ)^((log2 n+6)^2) := by
  let x := log2 n
  let y := log2 (36*(n:ℝ))
  let t := Nat.clog 2 (4*n+2)-1
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hx : 0≤x := div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Real.log_pos (by norm_num)).le
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hy : 0≤y := div_nonneg (Real.log_nonneg (by nlinarith : (1:ℝ)≤36*n)) (Real.log_pos (by norm_num)).le
  have ht : (t:ℝ)≤x+13/5 := collection_clog_minus_one n hn
  have hyb : y≤x+26/5 := by
    have he : y=log2 (36:ℝ)+x := by
      dsimp [y,x,log2]
      rw [Real.log_mul (by norm_num : (36:ℝ)≠0) hnR.ne']
      ring
    rw [he]
    linarith [log2_thirtysix_le]
  have hNx : (2:ℝ)^x=n := Real.rpow_logb (by norm_num) (by norm_num) hnR
  have hNy : (2:ℝ)^y=36*(n:ℝ) := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  have h4 : (2:ℝ)^(4*x)=(n:ℝ)^4 := by
    rw [show 4*x=x*4 by ring,Real.rpow_mul (by norm_num : (0:ℝ)≤2),hNx]
    norm_num
  have hty : (2:ℝ)^((t:ℝ)*y)=(36*(n:ℝ))^t := by
    rw [mul_comm,Real.rpow_mul (by norm_num : (0:ℝ)≤2),hNy,Real.rpow_natCast]
  have hF : ((uniformFarCap (4*n+2)+1:Nat):ℝ)≤5*(36*(n:ℝ))^t := by
    exact_mod_cast uniformFarCap_collection_bound n hn
  push_cast at hF
  have hbound : ((400*n^4*(uniformFarCap (4*n+2)+1):Nat):ℝ)≤
      (2:ℝ)^11*(n:ℝ)^4*(36*(n:ℝ))^t := by
    push_cast
    have h := mul_le_mul_of_nonneg_left hF (by positivity : (0:ℝ)≤400*(n:ℝ)^4)
    have hnonneg : (0:ℝ)≤(n:ℝ)^4*(36*(n:ℝ))^t := by positivity
    norm_num
    nlinarith
  have he : (2:ℝ)^11*(n:ℝ)^4*(36*(n:ℝ))^t=(2:ℝ)^(11+4*x+(t:ℝ)*y) := by
    rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num),h4,hty]
    norm_num
  have hprod : (t:ℝ)*y≤(x+13/5)*(x+26/5) :=
    mul_le_mul ht hyb hy (by linarith)
  have hexp : 11+4*x+(t:ℝ)*y≤(x+6)^2 := by nlinarith
  exact hbound.trans (by rw [he]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.log2_six_le
#print axioms Blueprint.HoughtonProof.log2_thirtysix_le
#print axioms Blueprint.HoughtonProof.collection_clog_minus_one
#print axioms Blueprint.HoughtonProof.collection_clog_power
#print axioms Blueprint.HoughtonProof.uniformFarCap_collection_bound
#print axioms Blueprint.HoughtonProof.collection_numeric_bound
