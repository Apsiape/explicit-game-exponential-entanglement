import Blueprint.RatesDefinitions
import QIT.Util.Matrix.JointDiagonalization

namespace Blueprint.FNormal
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators Function
set_option maxHeartbeats 600000

/-- The imaginary Hermitian part; no positivity or spectral hypothesis is added. -/
def imaginaryPart {d : Nat} (U : Mat d) : Mat d :=
  (-(Complex.I/2):ℂ) • (U-U.conjTranspose)

theorem imaginaryPart_hermitian {d : Nat} (U : Mat d) :
    (imaginaryPart U).IsHermitian := by
  change (imaginaryPart U).conjTranspose=imaginaryPart U
  simp only [imaginaryPart,Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  have hc : star (-(Complex.I/2):ℂ)=Complex.I/2 := by simp; ring
  rw [hc]
  module

theorem real_imaginary {d : Nat} (U : Mat d) :
    U=ReturnProof.hermitianPart U+Complex.I • imaginaryPart U := by
  simp only [ReturnProof.hermitianPart,imaginaryPart,smul_sub,smul_add,smul_smul]
  have hc : Complex.I * (-(Complex.I/2))=(1/2:ℂ) := by
    apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im]
  rw [hc]
  module

theorem parts_commute {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    Commute (ReturnProof.hermitianPart U) (imaginaryPart U) := by
  change _*_= _*_
  simp only [ReturnProof.hermitianPart,imaginaryPart,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_add]
  rw [hU.1,hU.2]
  module

theorem diagonalize {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    ∃ q : Mat d × (Fin d → ℂ), IsUnitary q.1 ∧ (∀ i, ‖q.2 i‖=1) ∧
      U=q.1*Matrix.diagonal q.2*q.1.conjTranspose := by
  let A : Bool → Mat d := fun b => if b then imaginaryPart U else ReturnProof.hermitianPart U
  have hA : ∀ b, (A b).IsHermitian := by
    intro b
    cases b
    · exact ReturnProof.hermitianPart_hermitian U
    · exact imaginaryPart_hermitian U
  have hC : Pairwise (Commute on A) := by
    intro i j hij
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact parts_commute U hU
    · exact (parts_commute U hU).symm
    · exact False.elim (hij rfl)
  let V : Mat d := QIT.jointUnitary hA hC
  let z : Fin d → ℂ := fun i =>
    (QIT.jointMatrixEigenvalues hA hC false i:ℂ)+Complex.I*(QIT.jointMatrixEigenvalues hA hC true i:ℂ)
  have hV : IsUnitary V := by
    exact (QIT.jointUnitary hA hC).property
  have hr := QIT.star_jointUnitary_mul_mul hA hC false
  have hi := QIT.star_jointUnitary_mul_mul hA hC true
  change V.conjTranspose*ReturnProof.hermitianPart U*V=
    Matrix.diagonal (fun i => (QIT.jointMatrixEigenvalues hA hC false i:ℂ)) at hr
  change V.conjTranspose*imaginaryPart U*V=
    Matrix.diagonal (fun i => (QIT.jointMatrixEigenvalues hA hC true i:ℂ)) at hi
  have hdiag : V.conjTranspose*U*V=Matrix.diagonal z := by
    rw [real_imaginary U]
    simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]
    rw [hr,hi]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [z]
    · simp [hij,Matrix.diagonal_apply_ne]
  have hback : U=V*Matrix.diagonal z*V.conjTranspose := by
    rw [←hdiag]
    simp only [←Matrix.mul_assoc,hV.2,Matrix.one_mul]
    rw [Matrix.mul_assoc,hV.2,Matrix.mul_one]
  have hDz : IsUnitary (Matrix.diagonal z) := by
    rw [←hdiag]
    exact ReturnProof.unitary_mul _ _
      (ReturnProof.unitary_mul _ _ (ReturnProof.unitary_adjoint V hV) hU) hV
  refine ⟨(V,z),hV,?_,hback⟩
  intro i
  have hi := congrArg (fun M : Mat d => M i i) hDz.1
  simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq,Matrix.one_apply_eq] at hi
  have hn : ‖z i‖^2=1 := by
    have hr := congrArg Complex.re hi
    simpa [Complex.mul_re,Complex.normSq_apply,Complex.sq_norm] using hr
  nlinarith [norm_nonneg (z i)]

end
end Blueprint.FNormal
