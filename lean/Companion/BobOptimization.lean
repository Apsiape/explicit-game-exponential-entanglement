import Companion.BobPayoffs

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def optimizedBob {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (j : Fin g.system.n) : Mat dB :=
  optimizedObservable (bobPayoff s j false) (bobPayoff s j true)
    (bobPayoff_positive s j false).isHermitian (bobPayoff_positive s j true).isHermitian

theorem optimizedBob_involution {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (j : Fin g.system.n) :
    IsInvolution (optimizedBob s j) := optimizedObservable_involution _ _ _ _

def optimizedBobStrategy {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) : Strategy g dA dB :=
  strategyWithBob s (fun j b => CountProof.symmetryProjection (optimizedBob s j) b)
    (fun j b => CountProof.symmetryProjection_positive _ (optimizedBob_involution s j) b)
    (fun j => by
      rw [add_comm]
      exact CountProof.symmetryProjection_sum _)

theorem optimizedBobStrategy_win {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    win s≤win (optimizedBobStrategy s) := by
  have hold := win_bob_objective s s.bob s.bob_positive s.bob_complete
  change win s=_ at hold
  have hnew := win_bob_objective s (fun j b => CountProof.symmetryProjection (optimizedBob s j) b)
    (fun j b => CountProof.symmetryProjection_positive _ (optimizedBob_involution s j) b)
    (fun j => by rw [add_comm]; exact CountProof.symmetryProjection_sum _)
  change win (optimizedBobStrategy s)=_ at hnew
  have hsum :
      (∑ j, ∑ b : Bool, (s.bob j b*bobPayoff s j b).trace.re)≤
        ∑ j, ∑ b : Bool, (CountProof.symmetryProjection (optimizedBob s j) b*bobPayoff s j b).trace.re := by
    apply Finset.sum_le_sum
    intro j _
    have h := binaryScore_optimized (bobPayoff s j false) (bobPayoff s j true) (s.bob j false) (s.bob j true)
      (bobPayoff_positive s j false).isHermitian (bobPayoff_positive s j true).isHermitian
      (s.bob_positive j false) (s.bob_positive j true) (s.bob_complete j)
    change binaryScore _ _ _ _≤binaryScore _ _
      (CountProof.symmetryProjection (optimizedBob s j) false)
      (CountProof.symmetryProjection (optimizedBob s j) true) at h
    simpa only [binaryScore,Matrix.trace_add,Complex.add_re,Fintype.sum_bool,add_comm] using h
  rw [hold,hnew]
  linarith

/-- Bob's full family of binary POVMs can be replaced simultaneously by
involutions on the same space and state, without decreasing game win. -/
theorem bob_projective_reduction {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    ∃ (t : Strategy g dA dB) (B : Fin g.system.n → Mat dB),
      t.psi=s.psi ∧ (∀ i a, t.alice i a=s.alice i a) ∧ win s≤win t ∧
      (∀ j, IsInvolution (B j)) ∧ (∀ j b, t.bob j b=CountProof.symmetryProjection (B j) b) :=
  ⟨optimizedBobStrategy s,optimizedBob s,rfl,fun _ _ => rfl,optimizedBobStrategy_win s,
    optimizedBob_involution s,fun _ _ => rfl⟩

/-- The first two transfer reductions, including compression of the given
strategy to Schmidt support before optimizing Bob's POVMs. -/
theorem support_projectiveBob_reduction {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    ∃ (r : Nat) (t : Strategy g dA r) (V : Matrix (Fin dB) (Fin r) ℂ) (B : Fin g.system.n → Mat r),
      r=s.psi.rank ∧ 0<r ∧ r≤dA ∧ r≤dB ∧ (t.psi*t.psi.conjTranspose).PosDef ∧
      V.conjTranspose*V=1 ∧ V*t.psi=s.psi ∧
      V*(t.psi*t.psi.conjTranspose)*V.conjTranspose=s.psi*s.psi.conjTranspose ∧
      win s≤win t ∧ (∀ j, IsInvolution (B j)) ∧
      (∀ j b, t.bob j b=CountProof.symmetryProjection (B j) b) := by
  obtain ⟨r,u,V,hr,hp,hA,hB,hpd,hV,hpsi,hrec,_,hwin⟩ := strategy_support_reduction s
  obtain ⟨t,B,ht,_,hw,hBi,he⟩ := bob_projective_reduction u
  exact ⟨r,t,V,B,hr,hp,hA,hB,ht.symm ▸ hpd,hV,ht.symm ▸ hpsi,ht.symm ▸ hrec,
    hwin ▸ hw,hBi,he⟩

end
end Companion.Analytic.TransferProof
