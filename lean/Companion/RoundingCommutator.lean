import Companion.RoundingGram

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem rounded_difference_normal {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    (roundUnitary U-U)*(roundUnitary U-U).conjTranspose=
      (roundUnitary U-U).conjTranspose*(roundUnitary U-U) := by
  let B := roundUnitary U
  have hB : IsInvolution B := roundUnitary_involution U
  have hc : B*U=U*B := (roundUnitary_commute U hU).eq
  have hs : U.conjTranspose*B=B*U.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hc
    simpa only [Matrix.conjTranspose_mul,hB.1] using h
  change (B-U)*(B-U).conjTranspose=(B-U).conjTranspose*(B-U)
  simp only [Matrix.conjTranspose_sub,hB.1,Matrix.mul_sub,Matrix.sub_mul,hB.2,hU.1,hU.2]
  rw [hc,hs]
  abel

theorem normal_adjoint_weighted_norm {d n : Nat} (A : Mat d) (X : Matrix (Fin d) (Fin n) ℂ)
    (hn : A*A.conjTranspose=A.conjTranspose*A) : hsNorm (A.conjTranspose*X)=hsNorm (A*X) := by
  have he : (A.conjTranspose*X).conjTranspose*(A.conjTranspose*X)=(A*X).conjTranspose*(A*X) := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _=X.conjTranspose*(A*A.conjTranspose)*X := by simp only [Matrix.mul_assoc]
      _=X.conjTranspose*(A.conjTranspose*A)*X := by rw [hn]
      _=_ := by simp only [Matrix.mul_assoc]
  rw [hsNorm,hsNorm,hsSquared_trace,hsSquared_trace,he]

theorem rounded_right_noise {d : Nat} (U xi : Mat d) (hU : IsUnitary U) (hxi : xi.IsHermitian) :
    hsNorm (xi*(roundUnitary U-U))=hsNorm ((roundUnitary U-U)*xi) := by
  rw [← hsNorm_conjTranspose (xi*(roundUnitary U-U)),Matrix.conjTranspose_mul,hxi.eq]
  exact normal_adjoint_weighted_norm _ _ (rounded_difference_normal U hU)

/-- Rounding changes the state commutator by at most twice the original
square-relator defect, with no strict-positivity assumption on xi. -/
theorem rounding_commutator_bound {d : Nat} (U xi : Mat d) (hU : IsUnitary U) (hxi : xi.IsHermitian) :
    hsNorm (comm (roundUnitary U) xi)≤hsNorm (comm U xi)+2*hsNorm ((U*U-1)*xi) := by
  have he : comm (roundUnitary U) xi=comm U xi+
      ((roundUnitary U-U)*xi-xi*(roundUnitary U-U)) := by
    simp only [comm,Matrix.sub_mul,Matrix.mul_sub]
    abel
  have h1 := hsNorm_add_le (comm U xi) ((roundUnitary U-U)*xi-xi*(roundUnitary U-U))
  rw [← he] at h1
  have h2 := CountProof.hs_sub_le ((roundUnitary U-U)*xi) (xi*(roundUnitary U-U))
  rw [rounded_right_noise U xi hU hxi] at h2
  have h3 := rounding_weighted_bound U hU xi
  linarith

def roundedGenerators {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (j : Fin g.system.n) : Mat d :=
  roundUnitary (m.U (j.val+1))

theorem model_generator_square_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (j : Fin g.system.n) :
    hsNorm ((m.U (j.val+1)*m.U (j.val+1)-1)*m.state.xi)≤e := by
  have h := m.relators (.square j.val) [pos j.val,pos j.val] (by simp [relator,j.isLt])
  simpa only [wordEval,pos,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,↓reduceIte,Matrix.mul_one,hs_eq_hsNorm] using h

theorem roundedGenerators_involution {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (j : Fin g.system.n) :
    IsInvolution (roundedGenerators m j) := roundUnitary_involution _

/-- The generator bounds used by return: rounding defect <=e and state
commutator <=3e. These estimates include the exact e=0 case. -/
theorem rounded_generators_estimates {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (j : Fin g.system.n) :
    hsNorm ((roundedGenerators m j-m.U (j.val+1))*m.state.xi)≤e ∧
      hsNorm (comm (roundedGenerators m j) m.state.xi)≤3*e := by
  have hs := model_generator_square_bound m j
  have hr := rounding_weighted_bound _ (m.unitary (j.val+1)) m.state.xi
  have hc := rounding_commutator_bound _ _ (m.unitary (j.val+1)) m.state.xi_positive.isHermitian
  have hm := m.state_commutators (j.val+1) (by omega) (by have hj:=j.isLt; omega)
  change hsNorm (comm (m.U (j.val+1)) m.state.xi)≤e at hm
  exact ⟨hr.trans hs,by
    change hsNorm (comm (roundUnitary (m.U (j.val+1))) m.state.xi)≤3*e
    linarith⟩

end
end Companion.Analytic.ReturnProof
