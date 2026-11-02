import Companion.BranchComposition

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem projection_coComplete {d : Nat} (Q : Mat d) (hQ : IsInvolution Q) :
    (∑ b : Bool, signProjection Q b*(signProjection Q b).conjTranspose)=1 := by
  change (∑ b : Bool, CountProof.symmetryProjection Q b*(CountProof.symmetryProjection Q b).conjTranspose)=1
  simpa only [CountProof.symmetryProjection_hermitian Q hQ.1] using CountProof.symmetryProjection_complete Q hQ

theorem sequential_branch_commutator {d : Nat} (n : Nat) (Q : Fin n → Mat d)
    (hQ : ∀ j, IsInvolution (Q j)) (eta : Mat d) :
    familyHS (fun a => comm (CountProof.jointProjection n Q a) eta)≤
      (∑ j, hsNorm (comm (Q j) eta))/Real.sqrt 2 := by
  induction n with
  | zero => simp [CountProof.jointProjection,comm,familyHS,stackMatrices,hsNorm,hsSquared]
  | succ n ih =>
    rw [familyHS_cube_cons]
    simp only [CountProof.jointProjection,Fin.tail_cons,Fin.cons_zero]
    change familyHS (fun t : Bool × (Fin n → Bool) =>
      comm (CountProof.jointProjection n (Fin.tail Q) t.2*signProjection (Q 0) t.1) eta)≤_
    rw [familyHS_swap (fun (b : Bool) (a : Fin n → Bool) =>
      comm (CountProof.jointProjection n (Fin.tail Q) a*signProjection (Q 0) b) eta)]
    have h := composition_commutator_bound
      (CountProof.jointProjection n (Fin.tail Q)) (signProjection (Q 0)) eta
      (CountProof.jointProjection_complete n _ (fun j => hQ j.succ))
      (projection_coComplete _ (hQ 0))
    rw [projection_commutator_norm] at h
    have hi := ih (Fin.tail Q) (fun j => hQ j.succ)
    rw [Fin.sum_univ_succ]
    rw [add_div]
    dsimp only [Fin.tail] at h hi ⊢
    linarith

theorem sequential_branch_commutator_uniform {d : Nat} (n : Nat) (Q : Fin n → Mat d)
    (hQ : ∀ j, IsInvolution (Q j)) (eta : Mat d) (c : ℝ)
    (hc : ∀ j, hsNorm (comm (Q j) eta)≤c) :
    familyHS (fun a => comm (CountProof.jointProjection n Q a) eta)≤(n:ℝ)*c/Real.sqrt 2 := by
  have h := sequential_branch_commutator n Q hQ eta
  have hs : (∑ j, hsNorm (comm (Q j) eta))≤(n:ℝ)*c := by
    simpa using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hc j)
  exact h.trans (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _))

end
end Companion.Analytic.ReturnProof
