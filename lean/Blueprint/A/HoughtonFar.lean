import Blueprint.A.HoughtonTransfer

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem halving_indices (n : Nat) (hn : 2<n) :
    let k := (n+1)/2
    let j := n-k
    2≤k ∧ 1≤j ∧ j≤k ∧ k<n ∧ j<n ∧ k+j=n := by
  dsimp
  omega

/-- The explicit halving recurrence for actual Johnson far-commutator
fillings. Every recursive argument is strictly smaller than the distance. -/
def farAreaBound (n : Nat) : Nat :=
  if hn : n≤2 then 1 else
    let k := (n+1)/2
    let j := n-k
    farAreaBound k + 2*j*(2*k+5+∑ l : Fin (k-2),farAreaBound (l.val+2)) +
      2*(∑ l : Fin j, (2*l.val+1+(∑ t : Fin l.val,farAreaBound (l.val-t.val+1))))
termination_by n
decreasing_by all_goals omega

theorem farAreaBound_small (n : Nat) (hn : n≤2) : farAreaBound n=1 := by
  rw [farAreaBound,dif_pos hn]

theorem farAreaBound_step (n : Nat) (hn : 2<n) :
    let k := (n+1)/2
    let j := n-k
    farAreaBound n=farAreaBound k+2*j*negativeBound farAreaBound k+2*transferBound farAreaBound j := by
  rw [farAreaBound,dif_neg (by omega)]
  simp only [negativeBound,transferBound,etaBound,←Fin.sum_univ_eq_sum_range]

/-- Every far commutator has a finite filling built from the five Johnson
relators. No Houghton presentation or Dehn-bound hypothesis is used. -/
theorem far_commutator_area (n : Nat) (hn : 2≤n) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ n)) (farAreaBound n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n≤2
    · have he : n=2 := by omega
      subst n
      rw [farAreaBound_small 2 (by omega)]
      exact alpha_sigma_two_area
    · let k := (n+1)/2
      let j := n-k
      have hij := halving_indices n (by omega)
      change 2≤k ∧ 1≤j ∧ j≤k ∧ k<n ∧ j<n ∧ k+j=n at hij
      have ha := ih k hij.2.2.2.1 hij.1
      have hb := negative_q_comm_area k hij.1 farAreaBound (fun m hm hmk =>
        ih m (lt_trans hmk hij.2.2.2.1) hm)
      have hu := qSigma_close j farAreaBound (fun m hm hmj =>
        ih m (lt_of_le_of_lt hmj hij.2.2.2.2.1) hm)
      have h := far_transfer_area k j (farAreaBound k) (negativeBound farAreaBound k)
        (transferBound farAreaBound j) ha hb hu
      rw [hij.2.2.2.2.2] at h
      rw [farAreaBound_step n (by omega)]
      exact h

theorem far_commutator_exists (n : Nat) (hn : 2≤n) :
    ∃ k, FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ n)) k :=
  ⟨farAreaBound n,far_commutator_area n hn⟩

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.halving_indices
#print axioms Blueprint.HoughtonProof.farAreaBound
#print axioms Blueprint.HoughtonProof.farAreaBound_small
#print axioms Blueprint.HoughtonProof.farAreaBound_step
#print axioms Blueprint.HoughtonProof.far_commutator_area
#print axioms Blueprint.HoughtonProof.far_commutator_exists
