import Companion.UniformCountModulus

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

theorem sum_nonzero_support {a : Type*} [Fintype a] (v : a → ℝ) (f : ℝ → ℝ) (hf : f 0=0) :
    (∑ j : {i // v i≠0}, f (v j.val))=∑ i, f (v i) := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => v i≠0) (fun i => f (v i))
  have hz : (∑ j : {i // ¬v i≠0}, f (v j.val))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [not_not.mp j.property,hf]
  rw [hz,add_zero] at h
  exact h

/-- The state on precisely the nonzero spectral coordinates. -/
def spectralState {d : Nat} (s : State d) :
    QIT.State {i // s.positive.isHermitian.eigenvalues i≠0} where
  matrix := Matrix.diagonal (fun i => (s.positive.isHermitian.eigenvalues i.val:ℂ))
  pos := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    exact_mod_cast s.positive.eigenvalues_nonneg i.val)
  trace_eq_one := by
    rw [Matrix.trace_diagonal]
    have he : (∑ i, (s.positive.isHermitian.eigenvalues i:ℂ))=1 :=
      s.positive.isHermitian.trace_eq_sum_eigenvalues.symm.trans s.normalized
    have hs := sum_nonzero_support s.positive.isHermitian.eigenvalues (fun x => x) rfl
    rw [← Complex.ofReal_sum,hs,Complex.ofReal_sum]
    exact he

theorem spectralState_entropy {d : Nat} (s : State d) :
    (spectralState s).vonNeumann=entropy s.rho := by
  rw [QIT.State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (spectralState s)
    (fun i => s.positive.isHermitian.eigenvalues i.val) rfl]
  rw [sum_nonzero_support _ QIT.xlog2 (by simp [QIT.xlog2])]
  rw [entropy_eq_quair]
  rfl

theorem state_rank_eq_spectral_card {d : Nat} (s : State d) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' s.rho))=
      Fintype.card {i // s.positive.isHermitian.eigenvalues i≠0} := by
  rw [Matrix.toLin'_apply']
  exact s.positive.isHermitian.rank_eq_card_non_zero_eigs

theorem state_rank_pos {d : Nat} (s : State d) :
    0<Module.finrank ℂ (LinearMap.range (Matrix.toLin' s.rho)) := by
  rw [state_rank_eq_spectral_card]
  exact Fintype.card_pos_iff.mpr (spectralState s).nonempty

theorem entropy_le_log_rank {d : Nat} (s : State d) :
    entropy s.rho≤Real.log (Module.finrank ℂ (LinearMap.range (Matrix.toLin' s.rho)))/Real.log 2 := by
  have h := (spectralState s).vonNeumann_le_log_card
  rw [spectralState_entropy] at h
  rw [state_rank_eq_spectral_card]
  exact h

theorem entropy_rank_lower {d : Nat} (s : State d) (t : ℝ) (ht : t≤entropy s.rho) :
    (2:ℝ)^t≤(Module.finrank ℂ (LinearMap.range (Matrix.toLin' s.rho)):ℝ) := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0:ℝ)<Module.finrank ℂ (LinearMap.range (Matrix.toLin' s.rho)) := by
    exact_mod_cast state_rank_pos s
  have h := (le_div_iff₀ hl).mp (ht.trans (entropy_le_log_rank s))
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  apply (Real.le_log_iff_exp_le hp).mp
  simpa only [mul_comm] using h

end
end Companion.Analytic.CountProof
