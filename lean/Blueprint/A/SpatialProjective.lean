import Blueprint.A.SpatialNaimark
import Blueprint.A.SpatialTransport

namespace Blueprint.SpatialProof
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def PVM {I : Type*} [Fintype I] (P : I → E →L[ℂ] E) : Prop := by
  classical
  exact (∀ a, (P a).adjoint=P a) ∧ (∀ a b, P a*P b=if a=b then P a else 0) ∧ ∑ a, P a=1

theorem pvm_positive {I : Type*} [Fintype I] (P : I → E →L[ℂ] E) (hP : PVM P) :
    ∀ a, positiveOperator (P a) := by
  intro a
  have hh := star_mul_self_nonneg (P a)
  change 0≤(P a).adjoint*P a at hh
  rw [hP.1 a,hP.2.1 a a,if_pos rfl] at hh
  exact (positive_iff _).mpr (ContinuousLinearMap.nonneg_iff_isPositive.mp hh)

def coarseEffect {I J : Type*} [Fintype I] [DecidableEq J] (f : I → J)
    (P : I → E →L[ℂ] E) (b : J) : E →L[ℂ] E := ∑ a, if f a=b then P a else 0

theorem coarse_pvm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (f : I → J) (P : I → E →L[ℂ] E) (hP : PVM P) : PVM (coarseEffect f P) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro b
    simp only [coarseEffect,map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    split <;> simp_all [hP.1]
  · intro b c
    have hrow (a : I) :
        (∑ a', (if f a=b then P a else 0)*(if f a'=c then P a' else 0))=
          if f a=b ∧ f a=c then P a else 0 := by
      rw [Finset.sum_eq_single a]
      · by_cases hb : f a=b <;> by_cases hc : f a=c <;> simp [hb,hc,hP.2.1 a a]
      · intro a' ha' hne
        split_ifs <;> simp_all [hP.2.1 a a',Ne.symm hne]
      · simp
    calc
      _=∑ a, ∑ a', (if f a=b then P a else 0)*(if f a'=c then P a' else 0) := by
        change ((∑ a, if f a=b then P a else 0)*(∑ a', if f a'=c then P a' else 0))=_
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      _=∑ a, if f a=b ∧ f a=c then P a else 0 := Finset.sum_congr rfl (fun a ha => hrow a)
      _=_ := by
        by_cases hbc : b=c
        · subst c
          simp only [and_self,↓reduceIte,coarseEffect]
        · have hn (a : I) : ¬(f a=b ∧ f a=c) := fun h => hbc (h.1.symm.trans h.2)
          simp only [hn,↓reduceIte,Finset.sum_const_zero,hbc]
  · simp only [coarseEffect]
    rw [Finset.sum_comm]
    simpa only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] using hP.2.2

theorem coarse_compression {I J : Type*} [Fintype I] [DecidableEq J]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (f : I → J) (P : I → K →L[ℂ] K) (A : I → E →L[ℂ] E) (V : E →L[ℂ] K)
    (h : ∀ a, V.adjoint ∘L P a ∘L V=A a) (b : J) :
    V.adjoint ∘L coarseEffect f P b ∘L V=coarseEffect f A b := by
  classical
  simp only [coarseEffect]
  change V.adjoint ∘L ((∑ a, if f a=b then P a else 0) ∘L V)=∑ a, if f a=b then A a else 0
  rw [ContinuousLinearMap.finsetSum_comp,ContinuousLinearMap.comp_finsetSum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hh : f a=b
  · simpa only [hh,↓reduceIte] using h a
  · simp only [hh,↓reduceIte,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.PVM
#print axioms Blueprint.SpatialProof.pvm_positive
#print axioms Blueprint.SpatialProof.coarseEffect
#print axioms Blueprint.SpatialProof.coarse_pvm
#print axioms Blueprint.SpatialProof.coarse_compression
