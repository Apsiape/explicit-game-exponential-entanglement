import Companion.ProjectionPinching
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem pinchingState_support (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) (rho : QIT.State a) :
    QIT.Matrix.Supports rho.matrix (pinchingState C hC rho).matrix := by
  have hN : (C*rho.matrix*C).PosSemidef := by
    simpa only [hC.1] using rho.pos.mul_mul_conjTranspose_same C
  have hs := QIT.Matrix.Supports.left_of_posSemidef_add rho.pos hN
  intro v hv
  rw [pinchingState_matrix,Matrix.smul_mulVec] at hv
  exact hs v ((smul_eq_zero.mp hv).resolve_left (by norm_num : (1/2:ℂ)≠0))

theorem entropy_logZero (rho : QIT.State a) :
    rho.vonNeumann=-(rho.matrix*cfc (fun x : ℝ => if x=0 then 0 else Real.log x) rho.matrix).trace.re/Real.log 2 := by
  have h := relativeEntropy_formula rho rho (QIT.Matrix.Supports.refl _)
  rw [relativeEntropy_self] at h
  have hz : -rho.vonNeumann-
      (rho.matrix*cfc (fun x : ℝ => if x=0 then 0 else Real.log x) rho.matrix).trace.re/Real.log 2=0 := by
    exact_mod_cast h.symm
  rw [neg_div]
  linarith only [hz]

/-- Pinching entropy gain equals the finite trace-log relative entropy,
including singular states and references. -/
theorem pinching_relativeEntropy (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1) (rho : QIT.State a) :
    rho.relativeEntropy (pinchingState C hC rho)=
      (((pinchingState C hC rho).vonNeumann-rho.vonNeumann:ℝ):EReal) := by
  let sigma := pinchingState C hC rho
  let f : ℝ → ℝ := fun x => if x=0 then 0 else Real.log x
  have hc : Commute sigma.matrix C := pinchingState_commute C hC rho
  have hf : Commute (cfc f sigma.matrix) C := hc.cfc_real f
  have ht : (sigma.matrix*cfc f sigma.matrix).trace=(rho.matrix*cfc f sigma.matrix).trace := by
    exact (congrArg (fun M : Matrix a a ℂ => Matrix.trace (M*cfc f sigma.matrix))
      (pinchingState_matrix C hC rho)).trans (trace_pinching_invariant C hC.2 rho.matrix _ hf)
  rw [relativeEntropy_formula rho sigma (pinchingState_support C hC rho)]
  change ((-rho.vonNeumann-(rho.matrix*cfc f sigma.matrix).trace.re/Real.log 2:ℝ):EReal)=_
  rw [← ht]
  have he := entropy_logZero sigma
  change sigma.vonNeumann=-(sigma.matrix*cfc f sigma.matrix).trace.re/Real.log 2 at he
  congr 1
  change -rho.vonNeumann-(sigma.matrix*cfc f sigma.matrix).trace.re/Real.log 2=sigma.vonNeumann-rho.vonNeumann
  rw [neg_div] at he
  linarith only [he]

theorem pinching_factor_bound {b : Type*} [Fintype b] [DecidableEq b]
    (C : Matrix a a ℂ) (hC : C.conjTranspose=C ∧ C*C=1)
    (K : Matrix a b ℂ) (hK : hsNorm K=1) (Z : Matrix.unitaryGroup b ℂ)
    (e : ℝ) (he0 : 0≤e) (he : hsNorm (K*(Z:Matrix b b ℂ)-C*K)≤e) :
    (pinchingState C hC (factorState K hK)).vonNeumann-(factorState K hK).vonNeumann≤
      binaryEntropy (min (e^2/4) (1/2)) := by
  have hZ : (Z:Matrix b b ℂ)*(Z:Matrix b b ℂ).conjTranspose=1 := Z.property.2
  have hleft : C.conjTranspose*C=1 := by rw [hC.1,hC.2]
  have h0 : hsNorm (K*(Z:Matrix b b ℂ))=1 := by rw [hsNorm_unitary_right _ _ hZ,hK]
  have h1 : hsNorm (C*K)=1 := by rw [hsNorm_unitary_left _ _ hleft,hK]
  have hs : factorState (K*(Z:Matrix b b ℂ)) h0=factorState K hK := by
    apply QIT.State.ext
    change (K*(Z:Matrix b b ℂ))*(K*(Z:Matrix b b ℂ)).conjTranspose=K*K.conjTranspose
    calc
      _=K*((Z:Matrix b b ℂ)*(Z:Matrix b b ℂ).conjTranspose)*K.conjTranspose := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _=_ := by rw [hZ,Matrix.mul_one]
  have hm : midpointState (factorState K hK) (factorState (C*K) h1)=pinchingState C hC (factorState K hK) := by
    apply QIT.State.ext
    simp only [midpointState,factorState,pinchingState_matrix,Matrix.conjTranspose_mul,hC.1,Matrix.mul_assoc]
  have h := quantum_jensen_shannon_of_distance_le (K*(Z:Matrix b b ℂ)) (C*K) h0 h1 e he0 he
  rw [hs,hm,pinching_relativeEntropy] at h
  exact_mod_cast h

end
end Companion.Analytic.CountProof
