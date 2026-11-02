import Blueprint.A.HashPrecision
import Mathlib.Data.Nat.Choose.Bounds

namespace Blueprint.AHash
noncomputable section
open Companion Concrete Companion.Analytic
open scoped Classical
set_option maxHeartbeats 600000

theorem hashPrecision_dimension (ell : Nat) (hell : 1≤ell) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    log2 (clockModelDimension (hashPrecisionM ell e) (hashPrecisionK ell e))≤
      336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8 := by
  have hb := hashPrecision_basic ell hell e he he1
  have hm := hashPrecision_m_bounds ell hell e he he1
  have hk := hashPrecision_k_bounds ell hell e he he1
  have hl : (1:ℝ)≤ell := by exact_mod_cast hell
  have he2 : 0<e^2 := sq_pos_of_pos he
  have hL2 : (ell:ℝ)/e^2≤(ell:ℝ)^2/e^2 := div_le_div_of_nonneg_right (by nlinarith) he2.le
  have hx : 0<2*(ell:ℝ)/e := lt_of_lt_of_le (by norm_num) hb.2.1
  have hclock : 2*(hashPrecisionM ell e:ℝ)+1≤9*(2*(ell:ℝ)/e)^2 := by
    calc
      _≤35*(ell:ℝ)/e^2 := by
        have hmm := hm.2.2.1
        simp only [mul_div_assoc] at hmm ⊢
        linarith [hb.1]
      _≤36*(ell:ℝ)^2/e^2 := by
        simp only [mul_div_assoc]
        nlinarith [hb.1]
      _=_ := by ring
  have h9 : log2 9≤7/2 := by
    have hh := hashLog_mono (by norm_num : (0:ℝ)<9^2) (by norm_num : (9:ℝ)^2≤2^7)
    rw [hashLog_pow,hashLog_pow,hashLog_two] at hh
    norm_num at hh
    linarith
  have hlog := hashLog_mono (by positivity : (0:ℝ)<2*(hashPrecisionM ell e:ℝ)+1) hclock
  rw [hashLog_mul (by norm_num) (ne_of_gt (sq_pos_of_pos hx)),hashLog_pow] at hlog
  have hclocklog : 2*log2 (2*(hashPrecisionM ell e:ℝ)+1)≤4*log2 (2*ell/e)+7 := by
    norm_num at hlog
    linarith
  have h6 : 6*(hashPrecisionM ell e:ℝ)+10≤112*(ell:ℝ)/e^2 := by
    have hmm := hm.2.2.1
    simp only [mul_div_assoc] at hmm ⊢
    linarith [hb.1]
  have hterm : (hashPrecisionK ell e:ℝ)*(6*hashPrecisionM ell e+10)≤
      336*ell/e^2*log2 (2*ell/e) := by
    calc
      _≤(3*log2 (2*ell/e))*(112*(ell:ℝ)/e^2) := by
        exact mul_le_mul hk.1 h6 (by positivity) (by linarith [hb.2.2])
      _=_ := by ring
  rw [clockModelDimension_log]
  linarith [hk.2.2]

theorem hashPrecision_dimension_second (ell : Nat) (hell : 1≤ell) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8≤
      400*(ell:ℝ)^2/e^2*log2 (2*ell/e) := by
  have hb := hashPrecision_basic ell hell e he he1
  have hl : (1:ℝ)≤ell := by exact_mod_cast hell
  have he2 : 0<e^2 := sq_pos_of_pos he
  have hL2 : (ell:ℝ)/e^2≤(ell:ℝ)^2/e^2 := div_le_div_of_nonneg_right (by nlinarith) he2.le
  have hB : 1≤(ell:ℝ)^2/e^2 := hb.1.trans hL2
  have hT : 0≤log2 (2*ell/e) := by linarith [hb.2.2]
  have hBT1 : (ell:ℝ)^2/e^2≤(ell:ℝ)^2/e^2*log2 (2*ell/e) := by
    exact le_mul_of_one_le_right (by positivity) hb.2.2
  have hBT2 : log2 (2*ell/e)≤(ell:ℝ)^2/e^2*log2 (2*ell/e) := by
    exact le_mul_of_one_le_left hT hB
  have hLT := mul_le_mul_of_nonneg_right hL2 hT
  simp only [mul_div_assoc] at *
  nlinarith

theorem clockModelFiniteHom_precision (ell : Nat) (hell : 1≤ell) (e : ℝ) (he : 0<e) (he1 : e≤1)
    (w : Published.HashWord) (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell) :
    normalizedHS ((clockModelFiniteHom (hashPrecisionM ell e) (hashPrecisionK ell e) (FreeGroup.mk w):
      Mat (clockModelDimension (hashPrecisionM ell e) (hashPrecisionK ell e)))-1)≤e := by
  let m := hashPrecisionM ell e
  let k := hashPrecisionK ell e
  let d := clockModelDimension m k
  let U := (clockModelHom m k (FreeGroup.mk w):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)
  have hm := hashPrecision_m_bounds ell hell e he he1
  have hh := clockModelHom_null_defect m k ell hm.1 hm.2.1 w hw hL
  have herror := hashPrecision_error ell hell e he he1
  have hs : hsNorm (U-1)^2≤e^2*d := hh.trans (mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg d))
  have hd : (0:ℝ)<d := by exact_mod_cast clockModelDimension_pos m k
  have hr := AGadget.reindex_defect (Fintype.equivFin (ClockModelIndex m k)) (clockModelHom m k (FreeGroup.mk w))
  have hn : normalizedHS ((clockModelFiniteHom m k (FreeGroup.mk w):Mat d)-(1:Mat d))=
      DoubleMatrix.defect (clockModelFiniteHom m k (FreeGroup.mk w)) := by
    simp only [normalizedHS,DoubleMatrix.defect,DoubleMatrix.sizeNorm,Fintype.card_fin,div_eq_mul_inv,mul_comm]
  change normalizedHS ((clockModelFiniteHom m k (FreeGroup.mk w):Mat d)-(1:Mat d))≤e
  rw [hn]
  change DoubleMatrix.defect
    ((AGadget.reindexUnitary (Fintype.equivFin (ClockModelIndex m k))) (clockModelHom m k (FreeGroup.mk w)))≤e
  rw [hr]
  change hsNorm (U-1)/Real.sqrt (d:ℝ)≤e
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hd)).mpr
  apply (sq_le_sq₀ (hsNorm_nonneg (U-1)) (mul_nonneg he.le (Real.sqrt_nonneg (d:ℝ)))).mp
  rw [mul_pow,Real.sq_sqrt hd.le]
  exact hs

end
end Blueprint.AHash

namespace Blueprint.Published
noncomputable section
open Companion Companion.Analytic AHash

/-- Proposition 9.4, with its original seven-letter alphabet, defect,
exact marker and both precision-dependent dimension inequalities. -/
theorem pauliHashModels : PauliHashModels := by
  intro W ell hell hL hW e he he1
  let m := hashPrecisionM ell e
  let k := hashPrecisionK ell e
  obtain ⟨hx,hz,hJ⟩ := clockModelFiniteHom_exact m k
  refine ⟨clockModelDimension m k,clockModelDimension_pos m k,clockModelFiniteHom m k,?_,hx,hz,hJ,?_,?_⟩
  · intro w hw
    exact clockModelFiniteHom_precision ell hell e he he1 w (hW w hw) (hL w hw)
  · exact hashPrecision_dimension ell hell e he he1
  · exact hashPrecision_dimension_second ell hell e he he1

end
end Blueprint.Published

#print axioms Blueprint.AHash.hashPrecision_dimension
#print axioms Blueprint.AHash.hashPrecision_dimension_second
#print axioms Blueprint.AHash.clockModelFiniteHom_precision
#print axioms Blueprint.Published.pauliHashModels
