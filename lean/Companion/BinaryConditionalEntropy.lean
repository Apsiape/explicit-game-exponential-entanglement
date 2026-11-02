import Companion.CountEntropyCost

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

/-- Conditional entropy contributed by a pair of masses, in bits.
Zero-mass pairs contribute zero. -/
def binaryMassEntropy (a b : ℝ) : ℝ := (a+b)*binaryEntropy (a/(a+b))

theorem binaryMassEntropy_log (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    binaryMassEntropy a b=(Real.negMulLog a+Real.negMulLog b-Real.negMulLog (a+b))/Real.log 2 := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0,binaryMassEntropy]
  have h1 : (a+b)*(a/(a+b))=a := mul_div_cancel₀ a hs
  have h2 : (a+b)*(1-a/(a+b))=b := by field_simp; ring
  have h := congrArg₂ (·+·) (Real.negMulLog_mul (a+b) (a/(a+b)))
    (Real.negMulLog_mul (a+b) (1-a/(a+b)))
  rw [h1,h2] at h
  rw [binaryMassEntropy,binaryEntropy,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [← mul_div_assoc]
  congr 1
  linarith only [h]

theorem binaryMassEntropy_symm (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    binaryMassEntropy a b=binaryMassEntropy b a := by
  rw [binaryMassEntropy_log a b ha hb,binaryMassEntropy_log b a hb ha]
  ring

/-- Mixing conditional binary laws increases their entropy, with no
strict-positivity assumption on the masses. -/
theorem binaryMassEntropy_superadd (a b c d : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    binaryMassEntropy a b+binaryMassEntropy c d≤binaryMassEntropy (a+c) (b+d) := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0,binaryMassEntropy]
  by_cases ht : c+d=0
  · have hc0 : c=0 := by linarith
    have hd0 : d=0 := by linarith
    simp [hc0,hd0,binaryMassEntropy]
  have hs0 : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  have ht0 : 0<c+d := lt_of_le_of_ne (add_nonneg hc hd) (Ne.symm ht)
  have hu : 0<a+b+(c+d) := add_pos hs0 ht0
  have h := Real.strictConcave_binEntropy.concaveOn.2
    (show a/(a+b) ∈ Set.Icc 0 1 from ⟨div_nonneg ha hs0.le,(div_le_one hs0).mpr (by linarith)⟩)
    (show c/(c+d) ∈ Set.Icc 0 1 from ⟨div_nonneg hc ht0.le,(div_le_one ht0).mpr (by linarith)⟩)
    (div_nonneg hs0.le hu.le) (div_nonneg ht0.le hu.le)
    (show (a+b)/(a+b+(c+d))+(c+d)/(a+b+(c+d))=1 by field_simp)
  have hm : (a+b)/(a+b+(c+d))*(a/(a+b))+
      (c+d)/(a+b+(c+d))*(c/(c+d))=(a+c)/(a+c+(b+d)) := by
    have hv : a+c+(b+d)≠0 := by linarith
    field_simp [hs,ht,ne_of_gt hu,hv]
    ring
  simp only [smul_eq_mul,hm] at h
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left h (div_nonneg hu.le hl.le)
  unfold binaryMassEntropy binaryEntropy
  convert hscaled using 1 <;> field_simp [ne_of_gt hu] <;> ring

/-- Binary conditional entropy versus the squared Hellinger distance of
the two masses. This includes the zero-mass case. -/
theorem binaryMassEntropy_hellinger (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    a+b-(Real.sqrt a-Real.sqrt b)^2/Real.log 2≤binaryMassEntropy a b := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0,binaryMassEntropy]
  have hs0 : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  have hx0 : 0≤a/(a+b) := div_nonneg ha hs0.le
  have hx1 : a/(a+b)≤1 := (div_le_one hs0).mpr (by linarith)
  have hr : (a+b)*Real.sqrt (a/(a+b)*(1-a/(a+b)))=Real.sqrt a*Real.sqrt b := by
    have he : a/(a+b)*(1-a/(a+b))=(a*b)/(a+b)^2 := by field_simp; ring
    rw [he,Real.sqrt_div (mul_nonneg ha hb),Real.sqrt_sq hs0.le,Real.sqrt_mul ha]
    exact mul_div_cancel₀ _ hs
  have h := mul_le_mul_of_nonneg_left (binary_hellinger (a/(a+b)) hx0 hx1) hs0.le
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have he : (a+b)*((1-2*Real.sqrt (a/(a+b)*(1-a/(a+b))))/Real.log 2)=
      (Real.sqrt a-Real.sqrt b)^2/Real.log 2 := by
    rw [← mul_div_assoc]
    congr 1
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb]
  rw [he] at h
  unfold binaryMassEntropy
  linarith

end
end Companion.Analytic.CountProof
