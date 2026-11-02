import Companion.MeasurementPadding
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace Companion.Analytic.ProfileProof
noncomputable section
open scoped BigOperators ENNReal
set_option maxHeartbeats 600000

theorem ennreal_quadratic_sInf (a : ℝ≥0∞) (ha0 : a≠0) (ha : a≠∞) (S : Set ℝ≥0∞) :
    a*(sInf S)^2=sInf ((fun x => a*x^2) '' S) := by
  by_cases hn : S.Nonempty
  · apply Monotone.map_csInf_of_continuousAt
      ((ENNReal.continuous_const_mul ha).comp (ENNReal.continuous_pow 2)).continuousAt
      (fun x y h => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ bot_le h 2) bot_le) hn
  · have hs : S=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hs,ENNReal.mul_top,ha0]

theorem strategy_loss_nonneg {g : LCS} {d : Nat} (s : Strategy g d d) : 0≤1-win s := by
  rw [← TransferProof.weighted_loss_sum]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (g.pi_nonneg i j) (sub_nonneg.mpr (TransferProof.pairWin_le_one s i j))))

theorem precision_profile_strategy {g : LCS} {d : Nat} (s : Strategy g d d) :
    modelPrecisionProfile g d≤ENNReal.ofReal (gameConstant g*Real.sqrt (1-win s)) := by
  obtain ⟨r,m,_,hr,_,_,_,_,_,V,hV,hrec⟩ := TransferProof.transfer g d d s (1-win s)
    (strategy_loss_nonneg s) (by linarith)
  unfold modelPrecisionProfile
  apply sInf_le
  refine ⟨r,transferPrecision g (1-win s),hr,TransferProof.transferPrecision_nonneg g _,⟨m⟩,?_⟩
  rw [precision_eq]

theorem precision_lower (g : LCS) (d : Nat) :
    (modelPrecisionProfile g d)^2/(ENNReal.ofReal (gameConstant g))^2≤gameLossProfile g d := by
  unfold gameLossProfile
  apply le_sInf
  rintro v ⟨s,rfl⟩
  have h := precision_profile_strategy s
  have hs := pow_le_pow_left₀ (by exact bot_le) h 2
  have hc := gameConstant_pos g
  calc
    _≤(ENNReal.ofReal (gameConstant g*Real.sqrt (1-win s)))^2/(ENNReal.ofReal (gameConstant g))^2 :=
      ENNReal.div_le_div_right hs _
    _=ENNReal.ofReal (1-win s) := by
      rw [ENNReal.ofReal_mul hc.le,mul_pow]
      rw [mul_comm,ENNReal.mul_div_cancel_right (pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hc)) (by simp)]
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,Real.sq_sqrt (strategy_loss_nonneg s)]

theorem precision_upper (g : LCS) (d : Nat) :
    gameLossProfile g d≤ENNReal.ofReal (returnConstant g.arity)*(modelPrecisionProfile g d)^2 := by
  unfold modelPrecisionProfile
  rw [ennreal_quadratic_sInf _ (ENNReal.ofReal_ne_zero_iff.mpr (ReturnProof.returnConstant_pos (arity_pos g))) (by simp)]
  apply le_sInf
  rintro v ⟨x,⟨r,e,hr,he,⟨m⟩,rfl⟩,rfl⟩
  obtain ⟨s,hs⟩ := strategy_padding (ReturnProof.returnMeasurementStrategy m) hr
  have hw := returned_win m he
  have hl : 1-win s≤returnConstant g.arity*e^2 := by rw [hs]; linarith
  calc
    _≤ENNReal.ofReal (1-win s) := by unfold gameLossProfile; exact sInf_le ⟨s,rfl⟩
    _≤ENNReal.ofReal (returnConstant g.arity*e^2) := ENNReal.ofReal_le_ofReal hl
    _=_ := by rw [ENNReal.ofReal_mul (ReturnProof.returnConstant_nonneg _),ENNReal.ofReal_pow he 2]

theorem twoSided : TwoSided := by
  intro g _
  refine ⟨?_,?_,?_⟩
  · intro eps he
    exact ⟨dimension_lower g eps he.le,dimension_upper g eps he.le⟩
  · intro eps he
    exact ⟨entropy_lower g eps he.le,entropy_upper g eps he.le⟩
  · intro d
    exact ⟨precision_lower g d,precision_upper g d⟩

end
end Companion.Analytic.ProfileProof
