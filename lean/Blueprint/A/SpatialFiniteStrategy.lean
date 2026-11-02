import Blueprint.A.SpatialLiterature
import Blueprint.MixedStates
import Companion.TransferModelBuilder

namespace Blueprint.SpatialProof
noncomputable section
open Companion Companion.Analytic Published TransferProof
open scoped BigOperators ComplexOrder MatrixOrder

theorem finite_operator_strategy (g : LCS) (h : FiniteOperatorSolution g) :
    ∃ a b, ∃ s : Strategy g a b, win s=1 := by
  obtain ⟨d,hd,B,hB,hcomm,hrow⟩ := h
  let st := MainProof.flatState d hd
  have hz : hs (0:Mat d)≤0 := by simp [hs]
  have hsc : ∀ j, hs (comm (B j) st.xi)≤0 := by
    intro j
    rw [MainProof.flatState_commutes hd]
    exact hz
  have hc : ∀ (i : Fin g.system.equations.length) (j k : Fin g.system.n),
      j.val∈(g.system.equations[i.val]).vars → k.val∈(g.system.equations[i.val]).vars →
      hs ((B j*B k*B j*B k-1)*st.xi)≤0 := by
    intro i j k hj hk
    have hh : B j*B k*B j*B k=1 := by
      calc
        _=B j*(B k*B j)*B k := by simp only [Matrix.mul_assoc]
        _=B j*(B j*B k)*B k := by rw [←hcomm i j k hj hk]
        _=(B j*B j)*(B k*B k) := by simp only [Matrix.mul_assoc]
        _=1 := by rw [(hB j).2,(hB k).2,Matrix.mul_one]
    rw [hh]
    exact TransferProof.zero_word_defect st.xi 0 le_rfl
  have hr : ∀ i : Fin g.system.equations.length,
      hs ((boolPhase (g.system.equations[i.val]).rhs •
        ((g.system.equations[i.val]).vars.map (TransferProof.naturalBob B)).prod-1)*st.xi)≤0 := by
    intro i
    have hh : boolPhase (g.system.equations[i.val]).rhs •
        ((g.system.equations[i.val]).vars.map (TransferProof.naturalBob B)).prod=(1:Mat d) := by
      rw [hrow i]
      cases (g.system.equations[i.val]).rhs <;> simp [boolPhase]
    rw [hh]
    exact TransferProof.zero_word_defect st.xi 0 le_rfl
  let m := TransferProof.modelFromSolutionBounds g st B 0 le_rfl hB hsc hc hr
  let s := ReturnProof.returnMeasurementStrategy m
  have hw : 1≤win s := by simpa using ProfileProof.returned_win m le_rfl
  exact ⟨d,d,s,le_antisymm (MixedStates.strategy_win_le_one s) hw⟩

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.finite_operator_strategy
