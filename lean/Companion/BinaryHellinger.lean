import Companion.Analytic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Companion.Analytic
noncomputable section
open Set
set_option maxHeartbeats 400000

def hellingerGap (x : ℝ) : ℝ := Real.binEntropy x-Real.log 2+1-2*Real.sqrt (x*(1-x))
def hellingerSlope (x : ℝ) : ℝ := Real.log (1-x)-Real.log x-(1-2*x)/Real.sqrt (x*(1-x))
def hellingerSecond (x : ℝ) : ℝ := (1-2*Real.sqrt (x*(1-x)))/(2*(x*(1-x))*Real.sqrt (x*(1-x)))

theorem hellingerGap_deriv (x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivAt hellingerGap (hellingerSlope x) x := by
  have hp : HasDerivAt (fun y : ℝ => y*(1-y)) (1-2*x) x := by
    convert (hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)) using 1
    · ext y <;> dsimp <;> ring
    · (try dsimp) <;> ring
  have hs := hp.sqrt (ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2)))
  convert (((Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (ne_of_lt hx.2)).sub
    (hasDerivAt_const x (Real.log 2))).add (hasDerivAt_const x (1:ℝ))).sub (hs.const_mul 2) using 1
  · rfl
  · dsimp [hellingerSlope]
    ring

theorem hellingerSlope_deriv (x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivAt hellingerSlope (hellingerSecond x) x := by
  have hp0 : 0<x*(1-x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hs0 : 0<Real.sqrt (x*(1-x)) := Real.sqrt_pos.mpr hp0
  have hs2 : (Real.sqrt (x*(1-x)))^2=x*(1-x) := Real.sq_sqrt hp0.le
  have hp : HasDerivAt (fun y : ℝ => y*(1-y)) (1-2*x) x := by
    convert (hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)) using 1
    · ext y <;> dsimp <;> ring
    · (try dsimp) <;> ring
  have hs := hp.sqrt (ne_of_gt hp0)
  have hn : HasDerivAt (fun y : ℝ => 1-2*y) (-2) x := by
    convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul 2) using 1
    · ext y <;> dsimp <;> ring
    · (try dsimp) <;> ring
  have hl := (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).log (ne_of_gt (sub_pos.mpr hx.2))).sub
    ((hasDerivAt_id x).log (ne_of_gt hx.1))
  convert hl.sub (hn.div hs (ne_of_gt hs0)) using 1
  · rfl
  · dsimp [hellingerSecond]
    field_simp [ne_of_gt hx.1,ne_of_gt (sub_pos.mpr hx.2),ne_of_gt hp0,ne_of_gt hs0]
    ring_nf
    rw [Real.sq_sqrt (show 0≤x-x^2 by nlinarith [hp0])]
    ring

theorem hellingerSecond_nonneg (x : ℝ) (hx : x ∈ Ioo 0 1) : 0≤hellingerSecond x := by
  have hp0 : 0<x*(1-x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hs0 := Real.sqrt_nonneg (x*(1-x))
  have hs2 := Real.sq_sqrt hp0.le
  have hhalf : Real.sqrt (x*(1-x))≤1/2 := by nlinarith [sq_nonneg (x-1/2)]
  exact div_nonneg (by linarith) (by positivity)

theorem hellingerGap_convex : ConvexOn ℝ (Icc 0 1) hellingerGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f':=hellingerSlope) (f'':=hellingerSecond)
    (convex_Icc 0 1) ?_ ?_ ?_ ?_
  · unfold hellingerGap
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact (hellingerGap_deriv x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hellingerSlope_deriv x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hellingerSecond_nonneg x hx

theorem hellingerGap_nonneg (x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) : 0≤hellingerGap x := by
  have hsym : hellingerGap (1-x)=hellingerGap x := by
    simp only [hellingerGap,Real.binEntropy_one_sub,sub_sub_cancel,mul_comm (1-x) x]
  have hhalf : hellingerGap (1/2)=0 := by
    have hs : Real.sqrt ((1/2:ℝ)*(1-1/2))=1/2 := by
      rw [show (1/2:ℝ)*(1-1/2)=(1/2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤1/2)]
    have hb : Real.binEntropy (1/2)=Real.log 2 := by simpa only [one_div] using Real.binEntropy_two_inv
    unfold hellingerGap
    rw [hs,hb]
    ring
  have h := hellingerGap_convex.2 ⟨hx0,hx1⟩ (show 1-x ∈ Icc 0 1 by constructor <;> linarith)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  have hm : (1/2:ℝ)*x+(1/2:ℝ)*(1-x)=1/2 := by ring
  simp only [smul_eq_mul,hm,hhalf,hsym] at h
  linarith

/-- The paper's binary Hellinger bound, with entropy measured in bits. -/
theorem binary_hellinger (x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) :
    1-binaryEntropy x≤(1-2*Real.sqrt (x*(1-x)))/Real.log 2 := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h := hellingerGap_nonneg x hx0 hx1
  unfold hellingerGap at h
  unfold binaryEntropy
  apply (le_div_iff₀ hl).mpr
  rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hl),one_mul]
  linarith

end
end Companion.Analytic
