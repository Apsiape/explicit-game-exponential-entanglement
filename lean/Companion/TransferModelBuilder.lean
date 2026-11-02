import Companion.PreparedTransferBounds

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem zero_word_defect {r : Nat} (xi : Mat r) (e : ℝ) (he : 0≤e) : hs (((1:Mat r)-1)*xi)≤e := by
  simpa only [sub_self,Matrix.zero_mul,hs,Matrix.zero_apply,Complex.normSq_zero,
    Finset.sum_const_zero,Real.sqrt_zero] using he

/-- All indexed solution-group relators are assembled from the square,
within-row commutator and ordered equation bounds. J is exactly -I. -/
def modelFromSolutionBounds (g : LCS) {r : Nat} (st : State r) (B : Fin g.system.n → Mat r)
    (e : ℝ) (he : 0≤e) (hB : ∀ j, IsInvolution (B j))
    (hsc : ∀ j, hs (comm (B j) st.xi)≤e)
    (hcomm : ∀ (i : Fin g.system.equations.length) (j k : Fin g.system.n),
      j.val ∈ (g.system.equations[i.val]).vars → k.val ∈ (g.system.equations[i.val]).vars →
      hs ((B j*B k*B j*B k-1)*st.xi)≤e)
    (hrow : ∀ i : Fin g.system.equations.length,
      hs ((boolPhase (g.system.equations[i.val]).rhs •
        ((g.system.equations[i.val]).vars.map (naturalBob B)).prod-1)*st.xi)≤e) : Model g r e where
  state := st
  U := solutionAssignment B
  unitary j := CountProof.involution_unitary _ (solutionAssignment_involution B hB j)
  relators := by
    intro key w hw
    cases key with
    | square j =>
      simp only [relator] at hw
      split at hw
      next hj =>
        cases Option.some.inj hw
        rw [wordEval_solution_square B hB ⟨j,hj⟩]
        exact zero_word_defect st.xi e he
      next => cases hw
    | centralSquare =>
      cases Option.some.inj hw
      rw [wordEval_solution_centralSquare]
      exact zero_word_defect st.xi e he
    | central j =>
      simp only [relator] at hw
      split at hw
      next hj =>
        cases Option.some.inj hw
        rw [wordEval_solution_central B hB ⟨j,hj⟩]
        exact zero_word_defect st.xi e he
      next => cases hw
    | equation row =>
      simp only [relator] at hw
      cases hg : g.system.equations[row]? with
      | none => simp only [hg,Option.bind_none] at hw; cases hw
      | some eqn =>
        simp only [hg,Option.bind_some] at hw
        change (if eqn.vars.all (· < g.system.n) then
          some ((if eqn.rhs then [pos g.system.n] else [])++eqn.vars.map pos) else none)=some w at hw
        split at hw
        next _ =>
          cases Option.some.inj hw
          obtain ⟨hrowidx,hEq⟩ := List.getElem?_eq_some_iff.mp hg
          subst eqn
          rw [wordEval_solution_row B _ _ (fun j hj => row_variable_bound g ⟨row,hrowidx⟩ j hj)]
          exact hrow ⟨row,hrowidx⟩
        next => cases hw
    | commute row j k =>
      simp only [relator] at hw
      cases hg : g.system.equations[row]? with
      | none => simp only [hg,Option.bind_none] at hw; cases hw
      | some eqn =>
        simp only [hg,Option.bind_some] at hw
        change (if j<g.system.n ∧ k<g.system.n ∧ j∈eqn.vars ∧ k∈eqn.vars then
          some [pos j,pos k,neg j,neg k] else none)=some w at hw
        split at hw
        next hcond =>
          cases Option.some.inj hw
          obtain ⟨hrowidx,hEq⟩ := List.getElem?_eq_some_iff.mp hg
          subst eqn
          rw [wordEval_solution_commute B hB ⟨j,hcond.1⟩ ⟨k,hcond.2.1⟩]
          exact hcomm ⟨row,hrowidx⟩ ⟨j,hcond.1⟩ ⟨k,hcond.2.1⟩ hcond.2.2.1 hcond.2.2.2
        next => cases hw
    | conjugacy _ => cases hw
    | pConjugacy _ => cases hw
  state_commutators := by
    intro j hj1 hjn
    by_cases hgen : j≤g.system.n
    · have hvalid : 1≤j ∧ j≤g.system.n := ⟨hj1,hgen⟩
      change hs (comm (solutionAssignment B j) st.xi)≤e
      unfold solutionAssignment
      rw [dite_eq_left hvalid]
      exact hsc _
    · have hj : j=g.system.n+1 := by omega
      subst j
      simp only [solutionAssignment_J,comm,Matrix.neg_mul,Matrix.mul_neg,Matrix.one_mul,Matrix.mul_one,sub_self]
      simpa only [hs,Matrix.zero_apply,Complex.normSq_zero,Finset.sum_const_zero,Real.sqrt_zero] using he
  central_visible := by
    simp only [solutionAssignment_J,neg_add_cancel,Matrix.zero_mul]
    simpa only [hs,Matrix.zero_apply,Complex.normSq_zero,Finset.sum_const_zero,Real.sqrt_zero] using he

end
end Companion.Analytic.TransferProof
