import Blueprint.A.SpatialProjective

namespace Blueprint.SpatialProof
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I]

theorem naimarkOutcome_mul (a b : I) : naimarkOutcome (E:=E) a*naimarkOutcome b=
    if a=b then naimarkOutcome a else 0 := by
  by_cases h : a=b
  · subst b
    simpa only [↓reduceIte] using naimarkOutcome_square (E:=E) a
  · simp only [h,↓reduceIte]
    by_cases ha : a=default <;> by_cases hb : b=default <;>
      simp_all [naimarkOutcome,add_mul,mul_add,blockProjection_mul,eq_comm]

theorem naimarkEffect_mul (A : I → E →L[ℂ] E)
    (hA : ∀ a, positiveOperator (A a)) (hAc : ∑ a, A a=1) (a b : I) :
    naimarkEffect A a*naimarkEffect A b=if a=b then naimarkEffect A a else 0 := by
  let U := naimarkSwap A
  have hU : U*U=1 := naimarkSwap_square A hA hAc
  change (U*naimarkOutcome a*U)*(U*naimarkOutcome b*U)=
    if a=b then U*naimarkOutcome a*U else 0
  calc
    _=U*(naimarkOutcome a*(U*U)*naimarkOutcome b)*U := by simp only [mul_assoc]
    _=U*(naimarkOutcome a*naimarkOutcome b)*U := by rw [hU]; simp only [mul_one]
    _=_ := by rw [naimarkOutcome_mul]; split <;> simp

theorem naimark_pvm (A : I → E →L[ℂ] E) (hA : ∀ a, positiveOperator (A a))
    (hAc : ∑ a, A a=1) : PVM (naimarkEffect A) := by
  refine ⟨naimarkEffect_adjoint A,?_,naimarkEffect_sum A hA hAc⟩
  intro a b
  by_cases h : a=b <;> simpa only [h,↓reduceIte] using naimarkEffect_mul A hA hAc a b

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.naimarkOutcome_mul
#print axioms Blueprint.SpatialProof.naimarkEffect_mul
#print axioms Blueprint.SpatialProof.naimark_pvm
