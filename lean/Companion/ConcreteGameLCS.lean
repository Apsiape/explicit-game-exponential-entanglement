import Companion.DefaultDistribution

namespace Companion.Analytic.MainProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 600000

theorem supplied_rows_nonempty : ∀ r∈suppliedGame.equations, r.vars≠[] := by
  have hc : suppliedGame.equations.all (fun r => decide (r.vars≠[]))=true := by decide
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp hc r hr)

theorem supplied_row_data (r : Equation) (hr : r∈suppliedGame.equations) :
    r.vars.length≤3 ∧ r.vars.Nodup ∧ ∀ j∈r.vars, j<suppliedGame.n := by
  have h := List.all_eq_true.mp game_wellFormed r hr
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

theorem supplied_rows_sorted : ∀ r∈suppliedGame.equations, r.vars.Pairwise (· < ·) := by
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp game_sorted r hr)

theorem supplied_rows_exist : suppliedGame.equations≠[] := by
  intro hh
  have h := game_dimensions.2
  rw [hh] at h
  contradiction

theorem supplied_arity_attained : ∃ r∈suppliedGame.equations, r.vars.length=3 := by
  refine ⟨⟨[0,5,8],false⟩,?_,rfl⟩
  decide

/-- The actual supplied numeric game with the paper's default distribution:
uniform equation, then uniform variable in that equation. -/
def concreteLCS : LCS := defaultLCS suppliedGame supplied_rows_nonempty
  (fun r hr => (supplied_row_data r hr).2.1) supplied_rows_sorted
  (fun r hr => (supplied_row_data r hr).2.2) supplied_rows_exist 3
  (fun r hr => (supplied_row_data r hr).1) supplied_arity_attained

theorem concreteLCS_system : concreteLCS.system=suppliedGame := rfl

theorem concreteLCS_arity : concreteLCS.arity=3 := rfl

theorem concreteLCS_piMin : concreteLCS.piMin=1/5061 := by
  change 1/((suppliedGame.equations.length:ℝ)*3)=1/5061
  rw [game_dimensions.2]
  norm_num

theorem concreteLCS_sizes : concreteLCS.system.n=1993 ∧ concreteLCS.system.equations.length=1687 :=
  game_dimensions

theorem concreteLCS_distribution (i : Fin concreteLCS.system.equations.length) (j : Fin concreteLCS.system.n) :
    concreteLCS.pi i j=if j.val∈(suppliedGame.equations[i.val]).vars then
      1/(1687*((suppliedGame.equations[i.val]).vars.length:ℝ)) else 0 := by
  change defaultPi suppliedGame i j=_
  unfold defaultPi
  have hm : (suppliedGame.equations.length:ℝ)=1687 := by exact_mod_cast game_dimensions.2
  rw [hm]

theorem concreteLCS_gameConstant : gameConstant concreteLCS=8*Real.sqrt 5061 := by
  unfold gameConstant
  rw [concreteLCS_arity,concreteLCS_piMin]
  norm_num

theorem concreteLCS_profiles :
      (∀ eps : ℝ, 0<eps →
        stateDimensionProfile concreteLCS (gameConstant concreteLCS*Real.sqrt eps)≤gameDimensionProfile concreteLCS eps ∧
        gameDimensionProfile concreteLCS eps≤stateDimensionProfile concreteLCS (Real.sqrt (eps/returnConstant 3))) ∧
      (∀ eps : ℝ, 0<eps →
        stateEntropyProfile concreteLCS (gameConstant concreteLCS*Real.sqrt eps)≤gameEntropyProfile concreteLCS eps ∧
        gameEntropyProfile concreteLCS eps≤stateEntropyProfile concreteLCS (Real.sqrt (eps/returnConstant 3))) ∧
      (∀ d : Nat,
        (modelPrecisionProfile concreteLCS d)^2/(ENNReal.ofReal (gameConstant concreteLCS))^2≤gameLossProfile concreteLCS d ∧
        gameLossProfile concreteLCS d≤ENNReal.ofReal (returnConstant 3)*(modelPrecisionProfile concreteLCS d)^2) := by
  refine ⟨?_,?_,?_⟩
  · intro eps he
    exact ⟨ProfileProof.dimension_lower _ _ he.le,ProfileProof.dimension_upper _ _ he.le⟩
  · intro eps he
    exact ⟨ProfileProof.entropy_lower _ _ he.le,ProfileProof.entropy_upper _ _ he.le⟩
  · intro d
    exact ⟨ProfileProof.precision_lower _ _,ProfileProof.precision_upper _ _⟩

end
end Companion.Analytic.MainProof
