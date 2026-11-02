import Companion.BobOptimization

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

variable {y z a : Type*} [Fintype y] [DecidableEq y] [Fintype z] [DecidableEq z]
  [Fintype a] [DecidableEq a]

def coarseEffect (P : QIT.ProjectiveMeasurement y a) (f : y → z) (b : z) : Matrix a a ℂ :=
  ∑ c, if f c=b then P.effects c else 0

theorem projective_effect_mul (P : QIT.ProjectiveMeasurement y a) (b c : y) :
    P.effects b*P.effects c=if b=c then P.effects b else 0 := by
  by_cases h : b=c
  · subst c; simp [P.idempotent]
  · simp only [h,↓reduceIte]; exact P.orthogonal b c h

theorem coarseEffect_positive (P : QIT.ProjectiveMeasurement y a) (f : y → z) (b : z) :
    (coarseEffect P f b).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro c _
  split
  · exact P.effect_posSemidef c
  · exact Matrix.PosSemidef.zero

theorem coarseEffect_mul_projection (P : QIT.ProjectiveMeasurement y a) (f : y → z) (b : z) (c : y) :
    coarseEffect P f b*P.effects c=if f c=b then P.effects c else 0 := by
  rw [coarseEffect,Matrix.sum_mul]
  calc
    _=∑ u, if u=c then (if f c=b then P.effects c else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : u=c
      · subst u
        simp [P.idempotent]
      · by_cases hf : f u=b <;> simp [hu,hf,projective_effect_mul]
    _=_ := by simp

theorem coarseEffect_mul (P : QIT.ProjectiveMeasurement y a) (f : y → z) (b c : z) :
    coarseEffect P f b*coarseEffect P f c=if b=c then coarseEffect P f b else 0 := by
  change coarseEffect P f b*(∑ u, if f u=c then P.effects u else 0)=_
  rw [Matrix.mul_sum]
  by_cases h : b=c
  · subst c
    simp only [↓reduceIte]
    change (∑ u, coarseEffect P f b*(if f u=b then P.effects u else 0))=
      ∑ u, if f u=b then P.effects u else 0
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : f u=b <;> simp [hu,coarseEffect_mul_projection]
  · simp only [h,↓reduceIte]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : f u=c
    · have hb : f u≠b := fun he => h (he.symm.trans hu)
      simp [hu,Ne.symm h,coarseEffect_mul_projection]
    · simp [hu]

theorem coarseEffect_complete (P : QIT.ProjectiveMeasurement y a) (f : y → z) :
    (∑ b, coarseEffect P f b)=1 := by
  unfold coarseEffect
  rw [Finset.sum_comm]
  simpa using P.sum_eq_one

def coarsePVM (P : QIT.ProjectiveMeasurement y a) (f : y → z) : QIT.ProjectiveMeasurement z a where
  effects := coarseEffect P f
  isHermitian b := (coarseEffect_positive P f b).isHermitian
  idempotent b := by simpa using coarseEffect_mul P f b b
  orthogonal b c h := by simpa only [h,↓reduceIte] using coarseEffect_mul P f b c
  sum_eq_one := coarseEffect_complete P f

theorem coarseEffect_compression {b : Type*} [Fintype b]
    (P : QIT.ProjectiveMeasurement y a) (f : y → z) (V : Matrix a b ℂ) (c : z) :
    V.conjTranspose*coarseEffect P f c*V=∑ u, if f u=c then V.conjTranspose*P.effects u*V else 0 := by
  simp only [coarseEffect,Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  split <;> simp_all

def validOutputMap (good : y → Prop) [DecidablePred good] (w : y) (c : y) : y :=
  if good c then c else w

theorem validOutputMap_good (good : y → Prop) [DecidablePred good] (w : y) (hw : good w) (c : y) :
    good (validOutputMap good w c) := by
  unfold validOutputMap
  split <;> assumption

theorem validOutputMap_fixed (good : y → Prop) [DecidablePred good] (w c : y) (hc : good c) :
    validOutputMap good w c=c := by simp [validOutputMap,hc]

theorem valid_coarseEffect_zero (P : QIT.ProjectiveMeasurement y a)
    (good : y → Prop) [DecidablePred good] (w : y) (hw : good w) (c : y) (hc : ¬good c) :
    coarseEffect P (validOutputMap good w) c=0 := by
  apply Finset.sum_eq_zero
  intro u _
  have he : validOutputMap good w u≠c := fun h => hc (h ▸ validOutputMap_good good w hw u)
  simp [he]

theorem valid_coarse_original (M : y → Matrix a a ℂ) (good : y → Prop) [DecidablePred good]
    (hz : ∀ u, ¬good u → M u=0) (w c : y) :
    (∑ u, if validOutputMap good w u=c then M u else 0)=M c := by
  calc
    _=∑ u, if u=c then M u else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : good u
      · rw [validOutputMap_fixed good w u hu]
      · simp [hz u hu]
    _=_ := by simp

end
end Companion.Analytic.TransferProof
