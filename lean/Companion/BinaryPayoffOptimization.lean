import Companion.HermitianOptimization

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def binaryScore {d : Nat} (F T QF QT : Mat d) : ℝ := (QF*F+QT*T).trace.re

def optimizedObservable {d : Nat} (F T : Mat d) (hF : F.IsHermitian) (hT : T.IsHermitian) : Mat d :=
  projectionInvolution (positiveSpectralProjector (F-T) (hF.sub hT))

theorem optimizedObservable_involution {d : Nat} (F T : Mat d) (hF : F.IsHermitian) (hT : T.IsHermitian) :
    IsInvolution (optimizedObservable F T hF hT) :=
  projectionInvolution_involution _ (positiveSpectralProjector_hermitian _ _) (positiveSpectralProjector_square _ _)

theorem binaryScore_difference {d : Nat} (F T QF QT : Mat d) (hq : QT+QF=1) :
    binaryScore F T QF QT=(QF*(F-T)).trace.re+T.trace.re := by
  have ht : QT=1-QF := eq_sub_of_add_eq hq
  simp only [binaryScore,ht,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.trace_add,
    Matrix.trace_sub,Complex.add_re,Complex.sub_re]
  ring

/-- Replacing an arbitrary binary POVM by the spectral-sign observable
does not decrease its Hermitian linear payoff. -/
theorem binaryScore_optimized {d : Nat} (F T QF QT : Mat d)
    (hF : F.IsHermitian) (hT : T.IsHermitian)
    (hQF : QF.PosSemidef) (hQT : QT.PosSemidef) (hq : QT+QF=1) :
    binaryScore F T QF QT≤binaryScore F T
      (CountProof.symmetryProjection (optimizedObservable F T hF hT) false)
      (CountProof.symmetryProjection (optimizedObservable F T hF hT) true) := by
  let P := positiveSpectralProjector (F-T) (hF.sub hT)
  have hc : (1-QF).PosSemidef := by rwa [← eq_sub_of_add_eq hq]
  have h := positiveSpectralProjector_optimal (F-T) QF (hF.sub hT) hQF hc
  change binaryScore F T QF QT≤binaryScore F T
    (CountProof.symmetryProjection (projectionInvolution P) false)
    (CountProof.symmetryProjection (projectionInvolution P) true)
  rw [projectionInvolution_effect,projectionInvolution_effect]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [binaryScore_difference F T QF QT hq,binaryScore_difference F T P (1-P) (by abel)]
  change (QF*(F-T)).trace.re≤(P*(F-T)).trace.re at h
  linarith

end
end Companion.Analytic.TransferProof
