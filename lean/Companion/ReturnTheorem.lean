import Companion.ReturnBranchEncoding
import Companion.ReturnConstants

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open TransferProof
set_option maxHeartbeats 600000

theorem rowBob_orderedProduct {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) :
    List.ofFn (rowBob m i)=(g.system.equations[i.val]).vars.map (naturalBob (roundedGenerators m)) := by
  conv_rhs => rw [← List.ofFn_getElem (xs:=(g.system.equations[i.val]).vars)]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  have hk : (g.system.equations[i.val]).vars[k.val]<g.system.n := (rowIndex g i k).isLt
  change roundedGenerators m (rowIndex g i k)=naturalBob (roundedGenerators m) (g.system.equations[i.val]).vars[k.val]
  unfold naturalBob
  rw [dite_eq_left hk]
  rfl

theorem row_tau_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (he : 0≤e)
    (i : Fin g.system.equations.length) :
    hsNorm (((List.ofFn (rowBob m i)).prod-boolPhase (g.system.equations[i.val]).rhs • (1:Mat d))*m.state.xi)≤
      (((g.system.equations[i.val]).vars.length:ℝ)^2+2)*e := by
  rw [rowBob_orderedProduct]
  exact rounded_parity_bound m he i

theorem return_loss_indexed {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (he : 0≤e)
    (i : Fin g.system.equations.length) (j : Fin (g.system.equations[i.val]).vars.length) :
    1-pairWin (returnMeasurementStrategy m) i (rowIndex g i j)≤returnConstant g.arity*e^2 := by
  let tau := hsNorm (((List.ofFn (rowBob m i)).prod-boolPhase (g.system.equations[i.val]).rhs • (1:Mat d))*m.state.xi)
  have hp := record_parity_bound (rowBob m i) (fun j => roundedGenerators_involution m _)
    (rowKraus m i) (CountProof.jointProjection_complete _ _
      (fun j => transpose_involution _ (roundedGenerators_involution m _))) m.state.xi (g.system.equations[i.val]).rhs
  change parityMass (rowKraus m i) m.state.xi (g.system.equations[i.val]).rhs≤
    (tau+∑ l, rowError m i l)^2/4 at hp
  have hl := return_pair_loss_raw_parity m i j
  have ha := return_loss_envelope
    (g.arity_upper _ (List.getElem_mem i.isLt)) j e he (rowError m i)
    (fun _ => familyHS_nonneg _) (rowError_bound m i) tau (hsNorm_nonneg _) (row_tau_bound m he i)
  linarith

/-- Full prescribed-measurement return, including singular states and e=0. -/
theorem returnTheorem : Return := by
  intro g d e m he
  refine ⟨returnMeasurementStrategy m,rfl,?_,?_,?_⟩
  · intro j b
    rfl
  · intro i a
    rfl
  · intro i j hj
    obtain ⟨k,hk⟩ := (rowIndex_range g i j).mpr hj
    rw [← hk]
    exact return_loss_indexed m he i k

theorem returnExistence : ReturnExistence := by
  intro g d e m he
  obtain ⟨s,hpsi,_,_,hbound⟩ := returnTheorem g d e m he.le
  exact ⟨s,hpsi,hbound⟩

end
end Companion.Analytic.ReturnProof
