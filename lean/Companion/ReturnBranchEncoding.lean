import Companion.ReturnSequentialBounds
import Companion.BranchProbabilities

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open TransferProof
set_option maxHeartbeats 600000

theorem validAnswer_rowRecord (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin (g.system.equations[i.val]).vars.length → Bool) :
    validAnswer g i (rowRecord g i a) ↔ recordParity a=(g.system.equations[i.val]).rhs := by
  have he : (g.system.equations[i.val]).vars.map (answerBit g (rowRecord g i a))=List.ofFn a := by
    conv_lhs => rw [← List.ofFn_getElem (xs:=(g.system.equations[i.val]).vars)]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    have hk : (g.system.equations[i.val]).vars[k.val]<g.system.n := (rowIndex g i k).isLt
    change answerBit g (rowRecord g i a) (g.system.equations[i.val]).vars[k.val]=a k
    unfold answerBit
    rw [dite_eq_left hk]
    exact rowRecord_apply g i a k
  unfold validAnswer recordParity
  rw [he]

theorem expectation_zero_left {d : Nat} (psi Q : Mat d) : expectation psi 0 Q=0 := by
  simp [expectation]

theorem sequentialAlice_expectation_sum {d : Nat} (g : LCS) (B : Fin g.system.n → Mat d)
    (i : Fin g.system.equations.length) (xi : Mat d) (Q : (Fin g.system.n → Bool) → Mat d) :
    (∑ out, expectation xi (sequentialAlice g B i out) (Q out))=
      ∑ a : Fin (g.system.equations[i.val]).vars.length → Bool,
        expectation xi ((sequentialKraus g B i (rowRecord g i a)).conjTranspose*
          sequentialKraus g B i (rowRecord g i a)) (Q (correctedAnswer g i (rowRecord g i a))) := by
  classical
  unfold sequentialAlice
  simp_rw [expectation_sum_left]
  rw [Finset.sum_comm]
  have h (a : Fin g.system.n → Bool) :
      (∑ out, expectation xi (if (∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false) ∧ correctedAnswer g i a=out
        then (sequentialKraus g B i a).conjTranspose*sequentialKraus g B i a else 0) (Q out))=
      if (∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false) then
        expectation xi ((sequentialKraus g B i a).conjTranspose*sequentialKraus g B i a) (Q (correctedAnswer g i a)) else 0 := by
    by_cases ha : ∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false
    · rw [ite_eq_left ha,Finset.sum_eq_single (correctedAnswer g i a)]
      · rw [ite_eq_left ⟨ha,rfl⟩]
      · intro out _ ho
        rw [ite_eq_right (fun h => ho h.2.symm),expectation_zero_left]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · rw [ite_eq_right ha]
      apply Finset.sum_eq_zero
      intro out _
      rw [ite_eq_right (fun h => ha h.1),expectation_zero_left]
  simp_rw [h]
  exact sum_canonical_records g i _

theorem return_pairWin_branches {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val∈(g.system.equations[i.val]).vars) :
    pairWin (returnMeasurementStrategy m) i j=
      ∑ a, hsNorm (signProjection (roundedGenerators m j)
        (correctedAnswer g i (rowRecord g i a) j)*rowFactor m i a)^2 := by
  unfold pairWin
  rw [ite_eq_left hj]
  change (∑ out, expectation m.state.xi (sequentialAlice g (roundedGenerators m) i out)
    (signProjection (roundedGenerators m j) (out j)))=_
  rw [sequentialAlice_expectation_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [kraus_projection_expectation m.state.xi (sequentialKraus g (roundedGenerators m) i (rowRecord g i a))
    (signProjection (roundedGenerators m j) (correctedAnswer g i (rowRecord g i a) j))
    (CountProof.symmetryProjection_hermitian _ (roundedGenerators_involution m j).1 _)
    (CountProof.symmetryProjection_square _ (roundedGenerators_involution m j).2 _)]
  rw [sequentialKraus_rowRecord,Matrix.mul_assoc]
  rfl

theorem rowFactor_normalized {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) : (∑ a, hsNorm (rowFactor m i a)^2)=1 := by
  change (∑ a, hsNorm (m.state.xi*(rowKraus m i a).transpose)^2)=1
  rw [← familyHS_sq,familyHS_right_parseval (fun a => (rowKraus m i a).transpose)
    (transposedKraus_coComplete _ (CountProof.jointProjection_complete _ _
      (fun j => transpose_involution _ (roundedGenerators_involution m _))))]
  change hs m.state.xi^2=1
  rw [state_xi_normalized]
  norm_num

theorem return_pair_loss_branches {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val∈(g.system.equations[i.val]).vars) :
    1-pairWin (returnMeasurementStrategy m) i j=
      ∑ a, hsNorm (signProjection (roundedGenerators m j)
        (!(correctedAnswer g i (rowRecord g i a) j))*rowFactor m i a)^2 := by
  rw [return_pairWin_branches m i j hj]
  have h := congrArg (fun F => ∑ a, F a) (funext (fun a =>
    binary_branch_complete (roundedGenerators m j) (rowFactor m i a) (roundedGenerators_involution m j)
      (correctedAnswer g i (rowRecord g i a) j)))
  rw [Finset.sum_add_distrib,rowFactor_normalized] at h
  linarith

theorem return_pair_loss_raw_parity {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j : Fin (g.system.equations[i.val]).vars.length) :
    1-pairWin (returnMeasurementStrategy m) i (rowIndex g i j)≤
      rowError m i j^2/4+parityMass (rowKraus m i) m.state.xi (g.system.equations[i.val]).rhs := by
  rw [return_pair_loss_branches m i _ (List.getElem_mem j.isLt)]
  have h := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) =>
    corrected_branch_bound g i (rowBob m i j) (rowFactor m i a) (roundedGenerators_involution m _)
      (rowRecord g i a) (rowIndex g i j))
  simp_rw [rowRecord_apply,binary_mismatch_identity,validAnswer_rowRecord] at h
  rw [Finset.sum_add_distrib] at h
  simp only [← Finset.sum_div,← familyHS_sq] at h
  simp_rw [binary_mismatch_identity]
  rw [← Finset.sum_div,← familyHS_sq]
  exact h

end
end Companion.Analytic.ReturnProof
