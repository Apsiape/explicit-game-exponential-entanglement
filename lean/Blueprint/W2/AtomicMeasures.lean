import Blueprint.FNormal
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Blueprint.W2
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
set_option maxHeartbeats 600000

def atomicMeasure {I α : Type*} [Fintype I] [MeasurableSpace α]
    (w : I → ℝ) (p : I → α) : Measure α :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (p i)

theorem atomic_probability {I α : Type*} [Fintype I] [MeasurableSpace α]
    (w : I → ℝ) (p : I → α) (hw : ∀ i, 0≤w i) (hsum : ∑ i, w i=1) :
    IsProbabilityMeasure (atomicMeasure w p) := by
  constructor
  simp only [atomicMeasure,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hsum]
  norm_num

theorem atomic_integral {I α : Type*} [Fintype I] [MeasurableSpace α] [MeasurableSingletonClass α]
    (w : I → ℝ) (p : I → α) (hw : ∀ i, 0≤w i) (f : α → ℝ) :
    (∫ x, f x ∂atomicMeasure w p)=∑ i, w i*f (p i) := by
  have hi (i : I) : Integrable f (ENNReal.ofReal (w i) • Measure.dirac (p i)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [atomicMeasure,integral_finsetSum_measure (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw i)]
  rfl

theorem atomic_fst {I J α β : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (w : I → J → ℝ) (x : I → α) (y : J → β) (hw : ∀ i j, 0≤w i j) :
    Measure.map Prod.fst (atomicMeasure (fun ij : I × J => w ij.1 ij.2) (fun ij => (x ij.1,y ij.2)))=
      atomicMeasure (fun i => ∑ j, w i j) x := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB]
  simp only [atomicMeasure,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply,
    smul_eq_mul,Fintype.sum_prod_type,Set.indicator_apply,Set.mem_preimage,Pi.one_apply]
  have hs (i : I) : ENNReal.ofReal (∑ j, w i j)=∑ j, ENNReal.ofReal (w i j) :=
    ENNReal.ofReal_sum_of_nonneg (fun j _ => hw i j)
  simp_rw [hs,Finset.sum_mul]

theorem atomic_snd {I J α β : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (w : I → J → ℝ) (x : I → α) (y : J → β) (hw : ∀ i j, 0≤w i j) :
    Measure.map Prod.snd (atomicMeasure (fun ij : I × J => w ij.1 ij.2) (fun ij => (x ij.1,y ij.2)))=
      atomicMeasure (fun j => ∑ i, w i j) y := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB]
  simp only [atomicMeasure,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply,
    smul_eq_mul,Fintype.sum_prod_type,Set.indicator_apply,Set.mem_preimage,Pi.one_apply]
  have hs (j : J) : ENNReal.ofReal (∑ i, w i j)=∑ i, ENNReal.ofReal (w i j) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i j)
  simp_rw [hs,Finset.sum_mul]
  exact Finset.sum_comm

end
end Blueprint.W2
