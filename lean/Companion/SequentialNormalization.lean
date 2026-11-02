import Companion.SequentialEncoding

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem transpose_involution {d : Nat} (B : Mat d) (hB : IsInvolution B) :
    IsInvolution B.transpose := by
  constructor
  · rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,hB.1]
  · rw [← Matrix.transpose_mul,hB.2,Matrix.transpose_one]

theorem sequentialAlice_complete {d : Nat} (g : LCS) (B : Fin g.system.n → Mat d)
    (hB : ∀ j, IsInvolution (B j)) (i : Fin g.system.equations.length) :
    (∑ a, sequentialAlice g B i a)=1 := by
  classical
  unfold sequentialAlice
  rw [Finset.sum_comm]
  have he (a : Fin g.system.n → Bool) :
      (∑ out, if (∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false) ∧ correctedAnswer g i a=out
        then (sequentialKraus g B i a).conjTranspose*sequentialKraus g B i a else 0)=
      if (∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false)
        then (sequentialKraus g B i a).conjTranspose*sequentialKraus g B i a else 0 := by
    by_cases ha : ∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false
    · have hc : (∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false)=True := propext (iff_true_intro ha)
      simp only [hc,true_and,↓reduceIte]
      rw [Finset.sum_eq_single (correctedAnswer g i a)]
      · exact ite_eq_left rfl
      · intro b _ hb
        exact ite_eq_right (Ne.symm hb)
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · have hc : (∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false)=False := propext (iff_false_intro ha)
      simp only [hc,false_and,↓reduceIte,Finset.sum_const_zero]
  simp_rw [he]
  rw [sum_canonical_records]
  simp_rw [sequentialKraus_rowRecord]
  exact CountProof.jointProjection_complete _ _ (fun k => transpose_involution _ (hB _))

theorem state_xi_normalized {d : Nat} (s : State d) : hs s.xi=1 := by
  change hsNorm s.xi=1
  have he : hsNorm s.xi^2=1 := by
    rw [hsNorm_sq,hsSquared_trace,s.xi_positive.isHermitian.eq,s.xi_square,s.normalized]
    rfl
  nlinarith [hsNorm_nonneg s.xi]

def returnMeasurementStrategy {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) : Strategy g d d where
  psi := m.state.xi
  normalized := state_xi_normalized m.state
  alice := sequentialAlice g (roundedGenerators m)
  alice_positive := sequentialAlice_positive g _
  alice_complete := sequentialAlice_complete g _ (roundedGenerators_involution m)
  alice_valid := sequentialAlice_invalid g _
  bob j := signProjection (roundedGenerators m j)
  bob_positive j := CountProof.symmetryProjection_positive _ (roundedGenerators_involution m j)
  bob_complete j := by
    change CountProof.symmetryProjection _ true+CountProof.symmetryProjection _ false=1
    rw [add_comm,CountProof.symmetryProjection_sum]

end
end Companion.Analytic.ReturnProof
