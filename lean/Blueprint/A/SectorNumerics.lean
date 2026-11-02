import Blueprint.Definitions

namespace Blueprint.ASectorProof
open Companion Companion.Analytic

theorem sector_length_constants (N L : Nat) (hN : 1≤N)
    (hL : 14000*N^2*max 3 N≤L) :
    63≤21*N*max 3 N ∧ 100*(21*N*max 3 N)≤L ∧ 42000≤L := by
  have hn : 3≤max 3 N := le_max_left _ _
  have hN2 : N≤N^2 := by nlinarith
  have hNN : 1≤N^2 := by nlinarith
  have h1 := Nat.mul_le_mul_left 3 hN
  have h2 := Nat.mul_le_mul_left N hn
  have h3 := Nat.mul_le_mul_right (max 3 N) hN2
  have h4 := Nat.mul_le_mul_right (max 3 N) hNN
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem scale_error_small (N : Nat) (e delta : ℝ) (he : 0<e) (hd : 0<delta)
    (hscale : (2:ℝ)^N*((2:ℝ)^((log2 N+23)^2))^4≤delta^2/(10200000*e^2)) : e≤delta/2 := by
  have hM : (1:ℝ)≤2^N := one_le_pow₀ (by norm_num)
  have hB : (1:ℝ)≤(2:ℝ)^((log2 N+23)^2) := Real.one_le_rpow (by norm_num) (sq_nonneg _)
  have hp : (1:ℝ)≤(2:ℝ)^N*((2:ℝ)^((log2 N+23)^2))^4 := by
    calc
      1=(1:ℝ)*1 := by norm_num
      _≤_ := mul_le_mul hM (one_le_pow₀ hB) (by norm_num) (by positivity)
  have hden : 0<10200000*e^2 := by positivity
  have hh := (le_div_iff₀ hden).mp (hp.trans hscale)
  nlinarith

theorem sector_numerators (ell L : Nat) (hell : 63≤ell) (hL : 100*ell≤L) (hlarge : 42000≤L)
    (e : ℝ) (he : 0≤e) :
    61*(L:ℝ)^2*e+26*ell*e+12*e≤63*(L:ℝ)^2*e ∧
    2*(10000*(ell:ℝ)^2*e)+6*(7*ell*e)+18*e≤63*(L:ℝ)^2*e ∧
    9*(10000*(ell:ℝ)^2*e)+24*(7*ell*e)+90*e≤63*(L:ℝ)^2*e := by
  have hl : (100:ℝ)*ell≤L := by exact_mod_cast hL
  have hll : (ell:ℝ)≤L := by nlinarith
  have hbig : (42000:ℝ)≤L := by exact_mod_cast hlarge
  have hs : (10000:ℝ)*(ell:ℝ)^2≤(L:ℝ)^2 := by
    have hh := (sq_le_sq₀ (by positivity : (0:ℝ)≤100*(ell:ℝ)) (by positivity : (0:ℝ)≤L)).mpr hl
    nlinarith only [hh]
  have hlow : (168:ℝ)*ell+90≤(L:ℝ)^2 := by nlinarith
  have hcross : (26:ℝ)*ell+12≤2*(L:ℝ)^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hcross he
  have h2 := mul_le_mul_of_nonneg_right hs he
  have h3 := mul_le_mul_of_nonneg_right hlow he
  constructor
  · nlinarith only [h1]
  · constructor <;> nlinarith [mul_nonneg (sq_nonneg (L:ℝ)) he]

theorem sector_division_bound (L : Nat) (e delta p : ℝ) (he : 0≤e) (hd : 0<delta)
    (hp : delta^2/16≤p) : (63*(L:ℝ)^2*e)/Real.sqrt p≤252*(L:ℝ)^2*e/delta := by
  have hp0 : 0<p := lt_of_lt_of_le (by positivity : (0:ℝ)<delta^2/16) hp
  have hq : 0<Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hqdelta : delta/4≤Real.sqrt p := by nlinarith [Real.sq_sqrt hp0.le]
  apply (div_le_div_iff₀ hq hd).mpr
  have hh := mul_le_mul_of_nonneg_left hqdelta (by positivity : (0:ℝ)≤252*(L:ℝ)^2*e)
  nlinarith only [hh]

theorem sector_precision (N L : Nat) (e delta : ℝ) (he : 0<e) (hd : 0<delta)
    (hL : (L:ℝ)≤(2:ℝ)^((log2 N+23)^2))
    (hscale : (2:ℝ)^N*((2:ℝ)^((log2 N+23)^2))^4≤delta^2/(10200000*e^2)) :
    16*((2^N:Nat):ℝ)*(252*(L:ℝ)^2*e/delta)^2≤1/10 := by
  have hden : 0<10200000*e^2 := by positivity
  have hpow : (L:ℝ)^4≤((2:ℝ)^((log2 N+23)^2))^4 := pow_le_pow_left₀ (by positivity) hL 4
  have hM : (0:ℝ)≤2^N := by positivity
  have hh := (mul_le_mul_of_nonneg_left hpow hM).trans hscale
  have hbound := (le_div_iff₀ hden).mp hh
  have heq : 16*(2:ℝ)^N*(252*(L:ℝ)^2*e/delta)^2=
      (16*252^2*(2:ℝ)^N*(L:ℝ)^4*e^2)/delta^2 := by ring
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have hnonneg : 0≤(2:ℝ)^N*(L:ℝ)^4*e^2 := by positivity
  nlinarith

end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.sector_length_constants
#print axioms Blueprint.ASectorProof.scale_error_small
#print axioms Blueprint.ASectorProof.sector_numerators
#print axioms Blueprint.ASectorProof.sector_division_bound
#print axioms Blueprint.ASectorProof.sector_precision
