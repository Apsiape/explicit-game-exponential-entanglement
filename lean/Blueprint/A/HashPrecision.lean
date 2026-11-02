import Blueprint.A.HashGlobalDefect
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds

namespace Blueprint.AHash
noncomputable section
open Companion Concrete Companion.Analytic
open scoped Classical
set_option maxHeartbeats 600000

def hashPrecisionM (ell : Nat) (e : ℝ) : Nat := ⌈16*ell/e^2⌉₊
def hashPrecisionK (ell : Nat) (e : ℝ) : Nat := ⌈2*log2 (2*ell/e)⌉₊

theorem hashLog_mono {x y : ℝ} (hx : 0<x) (hxy : x≤y) : log2 x≤log2 y := by
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos (by norm_num)).le

theorem hashLog_two : log2 2=1 := by unfold log2; exact div_self (Real.log_pos (by norm_num)).ne'

theorem hashLog_mul {x y : ℝ} (hx : x≠0) (hy : y≠0) : log2 (x*y)=log2 x+log2 y := by
  simp only [log2,Real.log_mul hx hy,add_div]

theorem hashLog_pow (x : ℝ) (n : Nat) : log2 (x^n)=n*log2 x := by
  simp only [log2,Real.log_pow,mul_div_assoc]

theorem clockModelDimension_log (m k : Nat) :
    log2 (clockModelDimension m k)=1+2*log2 (2*m+1)+(k:ℝ)*(6*m+10)+(2:ℝ)^k := by
  have hd : (clockModelDimension m k:ℝ)=
      2*(2*(m:ℝ)+1)^2*(2:ℝ)^(k*(6*m+10))*(2:ℝ)^(2^k) := by
    rw [clockModelDimension_formula]
    push_cast
    rfl
  rw [hd,hashLog_mul (by positivity) (by positivity),hashLog_mul (by positivity) (by positivity),
    hashLog_mul (by positivity) (by positivity),hashLog_pow,hashLog_pow,hashLog_pow,hashLog_two]
  push_cast
  ring

theorem hashPrecision_basic (ell : Nat) (hell : 1≤ell) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    1≤(ell:ℝ)/e^2 ∧ 2≤2*(ell:ℝ)/e ∧ 1≤log2 (2*ell/e) := by
  have hl : (1:ℝ)≤ell := by exact_mod_cast hell
  have he2 : 0<e^2 := sq_pos_of_pos he
  have he2le : e^2≤1 := by nlinarith
  have hL : 1≤(ell:ℝ)/e^2 := (le_div_iff₀ he2).mpr (by nlinarith)
  have hx : 2≤2*(ell:ℝ)/e := (le_div_iff₀ he).mpr (by nlinarith)
  exact ⟨hL,hx,by rw [←hashLog_two]; exact hashLog_mono (by norm_num) hx⟩

theorem hashPrecision_m_bounds (ell : Nat) (hell : 1≤ell) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    1≤hashPrecisionM ell e ∧ ell≤hashPrecisionM ell e ∧
      (hashPrecisionM ell e:ℝ)≤17*ell/e^2 ∧
      16*(ell:ℝ)/(2*hashPrecisionM ell e+1)≤e^2/2 := by
  have hb := hashPrecision_basic ell hell e he he1
  have hL := hb.1
  have hl : (1:ℝ)≤ell := by exact_mod_cast hell
  have he2 : 0<e^2 := sq_pos_of_pos he
  have he2le : e^2≤1 := by nlinarith
  have hlo : 16*(ell:ℝ)/e^2≤hashPrecisionM ell e := Nat.le_ceil _
  have hhi : (hashPrecisionM ell e:ℝ)<16*ell/e^2+1 := Nat.ceil_lt_add_one (by positivity)
  have hel : (ell:ℝ)≤(ell:ℝ)/e^2 := (le_div_iff₀ he2).mpr (by nlinarith)
  have hlo2 : 16*((ell:ℝ)/e^2)≤hashPrecisionM ell e := by simpa only [mul_div_assoc] using hlo
  have hmpos : (1:ℝ)≤hashPrecisionM ell e := by linarith
  have hmell : (ell:ℝ)≤hashPrecisionM ell e := by linarith
  refine ⟨by exact_mod_cast hmpos,by exact_mod_cast hmell,?_,?_⟩
  · calc
      _≤16*ell/e^2+(ell:ℝ)/e^2 := by linarith
      _=_ := by ring
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<2*hashPrecisionM ell e+1)).mpr
    have hh := (div_le_iff₀ he2).mp hlo
    nlinarith

theorem hashPrecision_k_bounds (ell : Nat) (hell : 1≤ell) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    (hashPrecisionK ell e:ℝ)≤3*log2 (2*ell/e) ∧
      4*(ell:ℝ)^2/e^2≤(2:ℝ)^hashPrecisionK ell e ∧
      (2:ℝ)^hashPrecisionK ell e≤8*(ell:ℝ)^2/e^2 := by
  have hb := hashPrecision_basic ell hell e he he1
  have hx : 0<2*(ell:ℝ)/e := lt_of_lt_of_le (by norm_num) hb.2.1
  have hlog : 0≤2*log2 (2*ell/e) := by linarith [hb.2.2]
  have hlo : 2*log2 (2*ell/e)≤hashPrecisionK ell e := Nat.le_ceil _
  have hhi : (hashPrecisionK ell e:ℝ)<2*log2 (2*ell/e)+1 := Nat.ceil_lt_add_one hlog
  have htarget : log2 ((2*(ell:ℝ)/e)^2)=2*log2 (2*ell/e) := by simpa only [Nat.cast_ofNat] using hashLog_pow (2*(ell:ℝ)/e) 2
  have hpower : (2:ℝ)^(2*log2 (2*ell/e))=(2*(ell:ℝ)/e)^2 := by
    rw [←htarget]
    exact Real.rpow_logb (by norm_num) (by norm_num) (sq_pos_of_pos hx)
  have hlowpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hlo
  have hhighpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hhi.le
  rw [Real.rpow_natCast,hpower] at hlowpow
  rw [Real.rpow_natCast,Real.rpow_add (by norm_num),hpower,Real.rpow_one] at hhighpow
  have hsq : (2*(ell:ℝ)/e)^2=4*(ell:ℝ)^2/e^2 := by ring
  refine ⟨by linarith [hb.2.2],by simpa only [hsq] using hlowpow,?_⟩
  calc
    _≤(2*(ell:ℝ)/e)^2*2 := hhighpow
    _=_ := by ring

theorem hashPrecision_error (ell : Nat) (hell : 1≤ell) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    4*(4*(ell:ℝ)/(2*hashPrecisionM ell e+1)+(ell.choose 2:ℝ)*(2:ℝ)^(-(hashPrecisionK ell e:ℤ)))≤e^2 := by
  have hm := hashPrecision_m_bounds ell hell e he he1
  have hk := hashPrecision_k_bounds ell hell e he he1
  have hchoose : (ell.choose 2:ℝ)≤(ell:ℝ)^2/2 := by
    have hc := Nat.choose_le_pow_div (α:=ℝ) 2 ell
    norm_num at hc
    exact hc
  have he2 : 0<e^2 := sq_pos_of_pos he
  have hpow : (0:ℝ)<(2:ℝ)^hashPrecisionK ell e := by positivity
  have hh := (div_le_iff₀ he2).mp hk.2.1
  have hcollision : 4*(ell.choose 2:ℝ)/(2:ℝ)^hashPrecisionK ell e≤e^2/2 := by
    apply (div_le_iff₀ hpow).mpr
    nlinarith
  rw [zpow_neg,zpow_natCast]
  calc
    4*(4*(ell:ℝ)/(2*hashPrecisionM ell e+1)+(ell.choose 2:ℝ)*((2:ℝ)^hashPrecisionK ell e)⁻¹)=
        16*(ell:ℝ)/(2*hashPrecisionM ell e+1)+4*(ell.choose 2:ℝ)/(2:ℝ)^hashPrecisionK ell e := by ring
    _≤e^2/2+e^2/2 := add_le_add hm.2.2.2 hcollision
    _=e^2 := by ring

end
end Blueprint.AHash

#print axioms Blueprint.AHash.hashPrecisionM
#print axioms Blueprint.AHash.hashPrecisionK
#print axioms Blueprint.AHash.hashLog_mono
#print axioms Blueprint.AHash.hashLog_two
#print axioms Blueprint.AHash.hashLog_mul
#print axioms Blueprint.AHash.hashLog_pow
#print axioms Blueprint.AHash.clockModelDimension_log
#print axioms Blueprint.AHash.hashPrecision_basic
#print axioms Blueprint.AHash.hashPrecision_m_bounds
#print axioms Blueprint.AHash.hashPrecision_k_bounds
#print axioms Blueprint.AHash.hashPrecision_error
