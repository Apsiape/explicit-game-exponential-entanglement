import Companion.ReturnTheorem
import Companion.TransferTheorem
import Companion.EntropyIsometry

namespace Companion.Analytic.ProfileProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder ENNReal
set_option maxHeartbeats 600000

theorem arity_pos (g : LCS) : 1≤g.arity := by
  obtain ⟨r,hr,he⟩ := g.arity_attained
  have h := List.length_pos_iff.mpr (g.rows_nonempty r hr)
  omega

theorem gameConstant_pos (g : LCS) : 0<gameConstant g := by
  have hm : (0:ℝ)<max (g.arity:ℝ) 4 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  exact div_pos (mul_pos (by norm_num) hm) (Real.sqrt_pos.mpr g.piMin_pos)

theorem precision_eq (g : LCS) (eps : ℝ) :
    transferPrecision g eps=gameConstant g*Real.sqrt eps := by
  unfold transferPrecision theta gameConstant
  rw [Real.sqrt_div' eps g.piMin_pos.le]
  ring

theorem return_precision_loss (g : LCS) (eps : ℝ) (he : 0≤eps) :
    returnConstant g.arity*(Real.sqrt (eps/returnConstant g.arity))^2=eps := by
  have hp := ReturnProof.returnConstant_pos (arity_pos g)
  rw [Real.sq_sqrt (div_nonneg he hp.le)]
  field_simp

theorem pair_loss_to_win {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (eps : ℝ) (he : 0≤eps)
    (h : ∀ i j, j.val∈(g.system.equations[i.val]).vars → 1-pairWin s i j≤eps) :
    1-eps≤win s := by
  have hl := TransferProof.weighted_loss_sum s
  have hb : (∑ i, ∑ j, g.pi i j*(1-pairWin s i j))≤eps := by
    calc
      _≤∑ i, ∑ j, g.pi i j*eps := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (g.pi_nonneg i j)
        by_cases hj : j.val∈(g.system.equations[i.val]).vars
        · exact h i j hj
        · simpa only [pairWin,hj,↓reduceIte,sub_self] using he
      _=eps := by simp_rw [← Finset.sum_mul]; rw [g.pi_normalized,one_mul]
  linarith

theorem returned_win {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (he : 0≤e) :
    1-returnConstant g.arity*e^2≤win (ReturnProof.returnMeasurementStrategy m) := by
  apply pair_loss_to_win _ _ (mul_nonneg (ReturnProof.returnConstant_nonneg _) (sq_nonneg _))
  intro i j hj
  obtain ⟨k,hk⟩ := (ReturnProof.rowIndex_range g i j).mpr hj
  rw [← hk]
  exact ReturnProof.return_loss_indexed m he i k

theorem returned_reduced {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) :
    (ReturnProof.returnMeasurementStrategy m).psi*(ReturnProof.returnMeasurementStrategy m).psi.conjTranspose=m.state.rho := by
  change m.state.xi*m.state.xi.conjTranspose=m.state.rho
  rw [m.state.xi_positive.isHermitian.eq,m.state.xi_square]

theorem state_isometry_entropy {r d : Nat} (rho : State r) (sigma : State d)
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (hs : sigma.rho=V*rho.rho*V.conjTranspose) : entropy sigma.rho=entropy rho.rho := by
  rw [entropy_eq_quair sigma,entropy_eq_quair rho]
  exact quair_entropy_isometry rho.toQuAIR sigma.toQuAIR V hV hs

theorem transfer_entropy {g : LCS} {d r : Nat} (s : Strategy g d d) (rho : State r)
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (hs : V*rho.rho*V.conjTranspose=s.psi*s.psi.conjTranspose) :
    entropy (s.psi*s.psi.conjTranspose)=entropy rho.rho :=
  state_isometry_entropy rho (State.ofQuAIR (CountProof.factorState s.psi s.normalized)) V hV hs.symm

end
end Companion.Analytic.ProfileProof
