import Blueprint.A.SpatialProjective

namespace Blueprint.SpatialProof
noncomputable section
open scoped BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem expect_coarse_sum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (psi : SpatialTensor E F) (f : I → J) (A : I → E →L[ℂ] E) (B : J → F →L[ℂ] F) :
    (∑ b, expect psi (coarseEffect f A b) (B b))=∑ a, expect psi (A a) (B (f a)) := by
  classical
  simp only [coarseEffect,expect_sum_left]
  have hh (a : I) (b : J) : expect psi (if f a=b then A a else 0) (B b)=
      if f a=b then expect psi (A a) (B b) else 0 := by
    split <;> simp_all [expect_zero_left]
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.expect_coarse_sum
