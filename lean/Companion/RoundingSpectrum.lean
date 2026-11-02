import Companion.TransferTheorem
import Companion.ReturnSpecification

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

def hermitianPart {d : Nat} (U : Mat d) : Mat d := (1/2:ℂ) • (U+U.conjTranspose)

theorem hermitianPart_hermitian {d : Nat} (U : Mat d) : (hermitianPart U).IsHermitian := by
  simp [hermitianPart,Matrix.IsHermitian,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,add_comm]

def roundingSign (x : ℝ) : ℝ := if 0≤x then 1 else -1

theorem hermitianSign_eq_projection {d : Nat} (H : Mat d) (hH : H.IsHermitian) :
    Unitary.conjStarAlgAut ℂ (Mat d) hH.eigenvectorUnitary
      (Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else -1))=
        TransferProof.projectionInvolution (TransferProof.positiveSpectralProjector H hH) := by
  let C := Unitary.conjStarAlgAut ℂ (Mat d) hH.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else 0)
  have he : Matrix.diagonal (fun i => if 0≤hH.eigenvalues i then (1:ℂ) else -1)=(2:ℂ) • D-1 := by
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases h : 0≤hH.eigenvalues i <;> norm_num [D,h,Matrix.diagonal_apply_eq]
    · simp [D,hij,Matrix.diagonal_apply_ne,Matrix.one_apply]
  change C _=(2:ℂ) • C D-1
  rw [he,map_sub,map_smul,map_one]

theorem roundUnitary_formula {d : Nat} (U : Mat d) :
    roundUnitary U=Unitary.conjStarAlgAut ℂ (Mat d) (hermitianPart_hermitian U).eigenvectorUnitary
      (Matrix.diagonal (fun i => if 0≤(hermitianPart_hermitian U).eigenvalues i then (1:ℂ) else -1)) := by
  unfold roundUnitary
  change (if h : (hermitianPart U).IsHermitian then _ else 1)=_
  rw [dite_eq_left (hermitianPart_hermitian U)]
  rfl

theorem roundUnitary_involution {d : Nat} (U : Mat d) : IsInvolution (roundUnitary U) := by
  rw [roundUnitary_formula,hermitianSign_eq_projection]
  exact TransferProof.projectionInvolution_involution _
    (TransferProof.positiveSpectralProjector_hermitian _ _) (TransferProof.positiveSpectralProjector_square _ _)

theorem roundUnitary_eq_cfc {d : Nat} (U : Mat d) : roundUnitary U=cfc roundingSign (hermitianPart U) := by
  rw [roundUnitary_formula,(hermitianPart_hermitian U).cfc_eq]
  unfold Matrix.IsHermitian.cfc
  apply congrArg (Unitary.conjStarAlgAut ℂ (Mat d) (hermitianPart_hermitian U).eigenvectorUnitary)
  apply congrArg Matrix.diagonal
  funext i
  dsimp only [Function.comp_def,roundingSign]
  split <;> simp

theorem roundUnitary_commute {d : Nat} (U : Mat d) (hU : IsUnitary U) : Commute (roundUnitary U) U := by
  have hc : Commute (hermitianPart U) U := by
    change hermitianPart U*U=U*hermitianPart U
    simp only [hermitianPart,Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,hU.1,hU.2]
  rw [roundUnitary_eq_cfc]
  exact hc.cfc_real roundingSign

theorem hermitianPart_complements_positive {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    (1+hermitianPart U).PosSemidef ∧ (1-hermitianPart U).PosSemidef := by
  have hh : (0:ℂ)≤1/2 := by constructor <;> norm_num
  have hp := (Matrix.posSemidef_conjTranspose_mul_self (1+U)).smul hh
  have hm := (Matrix.posSemidef_conjTranspose_mul_self (1-U)).smul hh
  have heP : (1/2:ℂ) • ((1+U).conjTranspose*(1+U))=1+hermitianPart U := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_one,Matrix.mul_add,Matrix.add_mul,
      Matrix.one_mul,Matrix.mul_one,hU.1,hermitianPart]
    module
  have heM : (1/2:ℂ) • ((1-U).conjTranspose*(1-U))=1-hermitianPart U := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.one_mul,Matrix.mul_one,hU.1,hermitianPart]
    module
  rw [heP] at hp
  rw [heM] at hm
  exact ⟨hp,hm⟩

theorem hermitianPart_eigenvalues_interval {d : Nat} (U : Mat d) (hU : IsUnitary U) (i : Fin d) :
    -1≤(hermitianPart_hermitian U).eigenvalues i ∧ (hermitianPart_hermitian U).eigenvalues i≤1 := by
  let E := (hermitianPart_hermitian U).eigenvectorUnitary
  let lam := (hermitianPart_hermitian U).eigenvalues
  have hE : (E:Mat d).conjTranspose*(E:Mat d)=1 := E.property.1
  have hd : (E:Mat d).conjTranspose*hermitianPart U*(E:Mat d)=Matrix.diagonal (fun j => (lam j:ℂ)) := by
    have h := (hermitianPart_hermitian U).conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_star_apply] at h
    exact h
  have hp := (hermitianPart_complements_positive U hU).1.mul_mul_conjTranspose_same (E:Mat d).conjTranspose
  have hm := (hermitianPart_complements_positive U hU).2.mul_mul_conjTranspose_same (E:Mat d).conjTranspose
  simp only [Matrix.conjTranspose_conjTranspose,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,
    Matrix.sub_mul,Matrix.mul_one,hE,hd] at hp hm
  have hp0 : (0:ℂ)≤(1+Matrix.diagonal (fun j => (lam j:ℂ))) i i := hp.diag_nonneg
  have hm0 : (0:ℂ)≤(1-Matrix.diagonal (fun j => (lam j:ℂ))) i i := hm.diag_nonneg
  have h1 := hp0.1
  have h2 := hm0.1
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.one_apply_eq,Matrix.diagonal_apply_eq,
    Complex.zero_re,Complex.add_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re] at h1 h2
  exact ⟨by linarith,by linarith⟩

end
end Companion.Analytic.ReturnProof
