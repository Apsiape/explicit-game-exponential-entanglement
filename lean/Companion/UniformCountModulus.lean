import Companion.UniformCountErrors
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

theorem binaryEntropy_fortieth :
    binaryEntropy (1/40)≤2/15+1/(40*Real.log 2) := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h40 : Real.log 40≤(16/3)*Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<40^3) (by norm_num : (40:ℝ)^3≤2^16)
    rw [Real.log_pow,Real.log_pow] at h
    norm_num at h
    linarith
  have h39 : Real.log ((40:ℝ)/39)≤1/39 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<40/39)
    linarith
  have he : binaryEntropy (1/40)=
      ((1/40)*Real.log 40+(39/40)*Real.log (40/39))/Real.log 2 := by
    norm_num [binaryEntropy,Real.binEntropy]
  rw [he]
  apply (div_le_iff₀ hl).mpr
  have hc : (2/15+1/(40*Real.log 2))*Real.log 2=(2/15)*Real.log 2+1/40 := by
    field_simp
  rw [hc]
  linarith

/-- The exact uniform numerical threshold used in the entropy corollary.
The logarithm estimates are kernel-checked Mathlib bounds. -/
theorem uniform_count_bracket (A B : ℝ) (hA0 : 0≤A) (hA : A≤1/10) (hB : B≤1/10) :
    (3/4:ℝ)≤1-B/(2*Real.log 2)-binaryEntropy (min (A/4) (1/2)) := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hx : min (A/4) (1/2) ∈ Set.Icc 0 (1/2) :=
    ⟨le_min (by linarith) (by norm_num),min_le_right _ _⟩
  have hxh : min (A/4) (1/2)≤1/40 := (min_le_left _ _).trans (by linarith)
  have hm := binaryEntropy_mono_half hx (by norm_num : (1/40:ℝ) ∈ Set.Icc 0 (1/2)) hxh
  have hb := div_le_div_of_nonneg_right hB (show (0:ℝ)≤2*Real.log 2 by positivity)
  have hn : (1/10:ℝ)/(2*Real.log 2)+1/(40*Real.log 2)≤7/60 := by
    have he : (1/10:ℝ)/(2*Real.log 2)+1/(40*Real.log 2)=3/(40*Real.log 2) := by ring
    rw [he]
    apply (div_le_iff₀ (mul_pos (by norm_num) hl)).mpr
    linarith [Real.log_two_gt_d9]
  have hh := binaryEntropy_fortieth
  linarith

end
end Companion.Analytic.CountProof
