import Companion.Analytic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith

namespace Companion.Analytic
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius

def hsSquared {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)
def hsNorm {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) : ℝ := Real.sqrt (hsSquared A)

theorem hsSquared_nonneg {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) : 0≤hsSquared A := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

theorem hsNorm_sq {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    (hsNorm A)^2=hsSquared A := Real.sq_sqrt (hsSquared_nonneg A)

theorem hs_eq_hsNorm {m n : Nat} (A : Matrix (Fin m) (Fin n) ℂ) : hs A=hsNorm A := rfl

theorem hsNorm_eq_frobenius {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    hsNorm A=‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  simp only [hsNorm,hsSquared,Complex.normSq_eq_norm_sq,Real.sqrt_eq_rpow,Real.rpow_two]

theorem hsNorm_nonneg {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) : 0≤hsNorm A :=
  Real.sqrt_nonneg _

theorem hsNorm_add_le {α β : Type*} [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    hsNorm (A+B)≤hsNorm A+hsNorm B := by
  simpa only [hsNorm_eq_frobenius] using norm_add_le A B

theorem hsSquared_trace {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    hsSquared A=(Matrix.trace (A.conjTranspose*A)).re := by
  simp only [hsSquared,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Complex.re_sum,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re]
  exact Finset.sum_comm

theorem hsSquared_conjTranspose {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    hsSquared A.conjTranspose=hsSquared A := by
  simp only [hsSquared,Matrix.conjTranspose_apply,Complex.star_def,Complex.normSq_conj]
  exact Finset.sum_comm

theorem hsNorm_conjTranspose {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    hsNorm A.conjTranspose=hsNorm A := by rw [hsNorm,hsNorm,hsSquared_conjTranspose]

theorem hsNorm_unitary_left {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (U : Matrix α α ℂ) (A : Matrix α β ℂ) (hU : U.conjTranspose*U=1) : hsNorm (U*A)=hsNorm A := by
  apply congrArg Real.sqrt
  rw [hsSquared_trace,hsSquared_trace]
  have he : (U*A).conjTranspose*(U*A)=A.conjTranspose*A := by
    rw [Matrix.conjTranspose_mul]
    calc
      A.conjTranspose*U.conjTranspose*(U*A) = A.conjTranspose*((U.conjTranspose*U)*A) := by
        simp only [Matrix.mul_assoc]
      _ = A.conjTranspose*A := by rw [hU,Matrix.one_mul]
  rw [he]

theorem hsNorm_unitary_right {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (U : Matrix β β ℂ) (A : Matrix α β ℂ) (hU : U*U.conjTranspose=1) : hsNorm (A*U)=hsNorm A := by
  rw [← hsNorm_conjTranspose (A*U),Matrix.conjTranspose_mul]
  rw [hsNorm_unitary_left U.conjTranspose A.conjTranspose (by simpa using hU),hsNorm_conjTranspose]

def asUnitary {d : Nat} (A : Mat d) (hA : IsUnitary A) : Matrix.unitaryGroup (Fin d) ℂ := ⟨A,hA⟩
def assignmentHom {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) :
    FreeGroup Nat →* Matrix.unitaryGroup (Fin d) ℂ := FreeGroup.lift fun j => asUnitary (U j) (hU j)

/-- The signed matrix-word encoding is exactly the corresponding free-group
homomorphism into the finite-dimensional unitary group. -/
theorem assignmentHom_word {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (w : Word) :
    ((assignmentHom U hU (FreeGroup.mk w) : Matrix.unitaryGroup (Fin d) ℂ) : Mat d)=wordEval U w := by
  induction w with
  | nil => simp [assignmentHom,FreeGroup.lift_mk,wordEval]
  | cons a w ih =>
    simp only [assignmentHom,FreeGroup.lift_mk,List.map_cons,List.prod_cons,Submonoid.coe_mul,
      wordEval] at *
    rw [ih]
    cases a.2 <;> rfl

theorem wordEval_unitary {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (w : Word) :
    IsUnitary (wordEval U w) := by
  rw [← assignmentHom_word U hU w]
  exact (assignmentHom U hU (FreeGroup.mk w)).property

end
end Companion.Analytic
