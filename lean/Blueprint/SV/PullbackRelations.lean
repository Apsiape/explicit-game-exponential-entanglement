import Blueprint.SV.PullbackBounds
import Blueprint.RatesDefinitions
import Blueprint.ASector

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators

theorem eval_inverse_word {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (w : Word) :
    wordEval U (FreeGroup.invRev w)=(wordEval U w).conjTranspose := by
  rw [←assignmentHom_word U hU,←FreeGroup.inv_mk,map_inv,←assignmentHom_word U hU w]
  rfl

theorem eval_comm_word {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (v w : Word) :
    wordEval U (ASector.commWord v w)=
      wordEval U v*wordEval U w*(wordEval U v).conjTranspose*(wordEval U w).conjTranspose := by
  simp only [ASector.commWord,TransferProof.wordEval_append,eval_inverse_word U hU]

theorem commutator_from_relator {d : Nat} (U W xi : Mat d) (hU : IsUnitary U) (hW : IsUnitary W) :
    hs (comm U W*xi)≤hs ((U*W*U.conjTranspose*W.conjTranspose-1)*xi)+
      2*(hs (comm U xi)+hs (comm W xi)) := by
  let R := U*W*U.conjTranspose*W.conjTranspose
  have hR : IsUnitary R := ReturnProof.unitary_mul _ _
    (ReturnProof.unitary_mul _ _ (ReturnProof.unitary_mul U W hU hW) (ReturnProof.unitary_adjoint U hU))
    (ReturnProof.unitary_adjoint W hW)
  have h := ReturnProof.unitary_difference_right_transport R 1 (W*U) xi hR
    (by simp [IsUnitary]) (ReturnProof.unitary_mul W U hW hU)
  have he : (R-1)*(W*U)*xi=comm U W*xi := by
    have heR : R*(W*U)=U*W := by
      calc
        _ = U*W*U.conjTranspose*(W.conjTranspose*W)*U := by simp only [R,Matrix.mul_assoc]
        _ = U*W*U.conjTranspose*U := by rw [hW.1,Matrix.mul_one]
        _ = U*W := by rw [Matrix.mul_assoc (U*W),hU.1,Matrix.mul_one]
    simp only [Analytic.comm,Matrix.sub_mul,Matrix.one_mul,heR]
  rw [he] at h
  have hc := ReturnProof.unitary_product_commutator W U xi hW hU
  simp only [hs_eq_hsNorm] at *
  linarith

theorem marker_visibility {d : Nat} (s : State d) (W Z : Mat d) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (b : ℝ) (hr : hs ((W*Z*W.conjTranspose*Z.conjTranspose+1)*s.xi)≤b)
    (hc : hs (comm Z s.xi)≤b) : 1-3/2*b≤hs ((W-1)*s.xi) := by
  let R := W*Z*W.conjTranspose*Z.conjTranspose
  have hconj := AWordArea.conjugation W.conjTranspose Z s.xi
    (ReturnProof.unitary_adjoint W hW) hZ
  rw [AWordArea.inverse_defect W s.xi hW] at hconj
  have hprod := AWordArea.product_defect W (Z*W.conjTranspose*Z.conjTranspose) s.xi hW
  have heq : W*(Z*W.conjTranspose*Z.conjTranspose)=R := by simp only [R,Matrix.mul_assoc]
  rw [heq] at hprod
  have ht := CountProof.hs_sub_le ((R+1)*s.xi) ((R-1)*s.xi)
  have he : (R+1)*s.xi-(R-1)*s.xi=(2:ℂ) • s.xi := by
    simp only [Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul]
    module
  rw [he,CountProof.hs_smul,show ‖(2:ℂ)‖=2 by norm_num,
    show hsNorm s.xi=1 from ReturnProof.state_xi_normalized s,mul_one] at ht
  change hs ((R+1)*s.xi)≤b at hr
  simp only [hs_eq_hsNorm] at *
  linarith

end
end Blueprint.SV

#print axioms Blueprint.SV.eval_inverse_word
#print axioms Blueprint.SV.eval_comm_word
#print axioms Blueprint.SV.commutator_from_relator
#print axioms Blueprint.SV.marker_visibility
