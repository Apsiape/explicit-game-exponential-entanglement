import Companion.Analytic
import QIT.Information.Fannes
import QIT.Information.Entropy.RelativeEntropyDPI

namespace Companion.Analytic
noncomputable section
open scoped BigOperators ComplexOrder

def State.toQuAIR {d : Nat} (s : State d) : QIT.State (Fin d) :=
  ⟨s.rho,s.positive,s.normalized⟩

/-- Every ordinary density matrix supplies the square-root data required by
the statement encoding; existence of that data is not an extra assumption. -/
def State.ofQuAIR {d : Nat} (s : QIT.State (Fin d)) : State d where
  rho := s.matrix
  positive := s.pos
  normalized := s.trace_eq_one
  xi := s.sqrtMatrix
  xi_positive := s.sqrtMatrix_pos
  xi_square := s.sqrtMatrix_mul_self

theorem State.toQuAIR_surjective (d : Nat) :
    Function.Surjective (State.toQuAIR : State d → QIT.State (Fin d)) := by
  intro s
  exact ⟨State.ofQuAIR s,by apply QIT.State.ext; rfl⟩

/-- The project's spectral entropy is exactly QuAIR's entropy in bits. -/
theorem entropy_eq_quair {d : Nat} (s : State d) :
    entropy s.rho=s.toQuAIR.vonNeumann := by
  have scalar (x : ℝ) : Real.negMulLog x/Real.log 2= -QIT.xlog2 x := by
    by_cases hx : x=0
    · simp [hx,Real.negMulLog,QIT.xlog2]
    · simp [Real.negMulLog,QIT.xlog2,QIT.log2,hx,div_eq_mul_inv,mul_assoc]
  rw [entropy,dite_eq_left s.positive.isHermitian]
  change (∑ i, Real.negMulLog (s.positive.isHermitian.eigenvalues i))/Real.log 2=
    -(∑ i, QIT.xlog2 (s.positive.isHermitian.eigenvalues i))
  rw [Finset.sum_div]
  simp_rw [scalar]
  rw [Finset.sum_neg_distrib]

theorem entropy_nonneg {d : Nat} (s : State d) : 0≤entropy s.rho := by
  rw [entropy_eq_quair]
  exact s.toQuAIR.vonNeumann_nonneg

theorem entropy_le_log_dimension {d : Nat} (s : State d) :
    entropy s.rho≤Real.log d/Real.log 2 := by
  rw [entropy_eq_quair]
  simpa [QIT.log2] using s.toQuAIR.vonNeumann_le_log_card

/-- Imported HOW Fannes modulus, after identifying both entropy definitions.
The distance here is the unnormalized trace norm, as in the audited library API. -/
theorem entropy_fannes {d : Nat} (s t : State d) :
    |entropy s.rho-entropy t.rho|≤
      QIT.log2 d*QIT.howFannesEta (s.toQuAIR.traceNormDistance t.toQuAIR) := by
  rw [entropy_eq_quair,entropy_eq_quair]
  simpa using QIT.State.vonNeumann_dist_le_howFannes s.toQuAIR t.toQuAIR

/-- Canonical trace-log/support relative entropy, with QuAIR's extended-real
infinity convention, decreases under a finite-dimensional quantum channel. -/
theorem state_dataProcessing {d r : Nat} (s t : State d) (Phi : QIT.Channel (Fin d) (Fin r)) :
    s.toQuAIR.relativeEntropy t.toQuAIR ≥
      (Phi.applyState s.toQuAIR).relativeEntropy (Phi.applyState t.toQuAIR) :=
  QIT.State.relativeEntropy_dataProcessing_channel_ge _ _ _

end
end Companion.Analytic
