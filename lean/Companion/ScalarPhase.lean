import Companion.DoubleMatrix

namespace Companion.ScalarPhase
noncomputable section
open DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

def minusOne (α : Type) [Fintype α] [DecidableEq α] : U α :=
  ⟨-1,by
    change (-1:Matrix α α ℂ).conjTranspose*(-1)=1 ∧
      (-1:Matrix α α ℂ)*(-1:Matrix α α ℂ).conjTranspose=1
    simp⟩

theorem square : minusOne α*minusOne α=1 := by
  apply Subtype.ext
  change (-1:Matrix α α ℂ)*(-1)=1
  simp
theorem inverse : (minusOne α)⁻¹=minusOne α := inv_eq_of_mul_eq_one_left square
theorem central (A : U α) : Commute A (minusOne α) := by
  change A*minusOne α=minusOne α*A
  apply Subtype.ext
  change (A:Matrix α α ℂ)*(-1)=(-1)*(A:Matrix α α ℂ)
  simp

theorem copy : DoubleMatrix.copy (minusOne α)=minusOne (Bool × α) := by
  apply Subtype.ext
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> simp [DoubleMatrix.copy,mono,matrix,minusOne,Matrix.one_apply,Prod.mk.injEq]

theorem swap_square : swap α*swap α=1 := by
  simp [swap,mono_mul,mono_one]
theorem switch : swap α*diag (minusOne α) 1*swap α=diag 1 (minusOne α) := by
  simp [swap,mono_mul]
theorem diagonal_product : diag (minusOne α) 1*diag 1 (minusOne α)=minusOne (Bool × α) := by
  rw [mono_mul]
  simpa [DoubleMatrix.copy] using (copy (α:=α))
theorem u_square : diag 1 (minusOne α)*diag 1 (minusOne α)=1 := by
  simpa [mono_mul,square] using (mono_one (α:=α))

end
end Companion.ScalarPhase
