import Companion.ConcreteGameLCS
import Companion.AreaEstimate
import QIT.States.MaximallyMixed

namespace Companion.Analytic.MainProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 600000

def flatState (d : Nat) (hd : 0<d) : State d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact State.ofQuAIR (QIT.State.maximallyMixed (Fin d))

theorem flatState_rho (d : Nat) (hd : 0<d) :
    (flatState d hd).rho=(((d:ℝ)⁻¹:ℝ):ℂ) • (1:Mat d) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  change (QIT.State.maximallyMixed (Fin d)).matrix=_
  simp only [QIT.State.maximallyMixed_matrix,Fintype.card_fin]

theorem flatState_xi (d : Nat) (hd : 0<d) :
    (flatState d hd).xi=(((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • (1:Mat d) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  change (QIT.State.maximallyMixed (Fin d)).sqrtMatrix=_
  simpa only [Fintype.card_fin,Real.sqrt_inv] using QIT.State.maximallyMixed_sqrtMatrix (a:=Fin d)

theorem flatState_weighted_norm {d : Nat} (hd : 0<d) (A : Mat d) :
    hs (A*(flatState d hd).xi)=normalizedHS A := by
  rw [flatState_xi,Matrix.mul_smul,Matrix.mul_one]
  change hsNorm ((((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • A)=_
  simp only [normalizedHS,hsNorm_eq_frobenius,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]

theorem flatState_commutes {d : Nat} (hd : 0<d) (A : Mat d) : comm A (flatState d hd).xi=0 := by
  rw [flatState_xi]
  simp only [comm,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,sub_self]

def flatModel (g : LCS) (d : Nat) (hd : 0<d) (U : Nat → Mat d)
    (hU : ∀ j, IsUnitary (U j)) (e : ℝ) (he : 0≤e)
    (hR : ∀ k r, relator g.system k=some r → normalizedHS (wordEval U r-1)≤e)
    (hJ : U (g.system.n+1)=-1) : Model g d e where
  state := flatState d hd
  U := U
  unitary := hU
  relators k r hr := by rw [flatState_weighted_norm]; exact hR k r hr
  state_commutators j _ _ := by
    rw [flatState_commutes]
    simpa only [hs,Matrix.zero_apply,Complex.normSq_zero,Finset.sum_const_zero,Real.sqrt_zero] using he
  central_visible := by
    rw [hJ,neg_add_cancel,Matrix.zero_mul]
    simpa only [hs,Matrix.zero_apply,Complex.normSq_zero,Finset.sum_const_zero,Real.sqrt_zero] using he

theorem flat_return_strategy (g : LCS) (d : Nat) (hd : 0<d) (U : Nat → Mat d)
    (hU : ∀ j, IsUnitary (U j)) (e : ℝ) (he : 0≤e)
    (hR : ∀ k r, relator g.system k=some r → normalizedHS (wordEval U r-1)≤e)
    (hJ : U (g.system.n+1)=-1) :
    ∃ s : Strategy g d d,
      s.psi=(((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • (1:Mat d) ∧
      s.psi*s.psi.conjTranspose=(((d:ℝ)⁻¹:ℝ):ℂ) • (1:Mat d) ∧
      (∀ i j, j.val∈(g.system.equations[i.val]).vars → 1-pairWin s i j≤returnConstant g.arity*e^2) ∧
      1-returnConstant g.arity*e^2≤win s := by
  let m := flatModel g d hd U hU e he hR hJ
  refine ⟨ReturnProof.returnMeasurementStrategy m,flatState_xi d hd,?_,?_,ProfileProof.returned_win m he⟩
  · rw [ProfileProof.returned_reduced]
    exact flatState_rho d hd
  · intro i j hj
    obtain ⟨k,hk⟩ := (ReturnProof.rowIndex_range g i j).mpr hj
    rw [← hk]
    exact ReturnProof.return_loss_indexed m he i k

end
end Companion.Analytic.MainProof
