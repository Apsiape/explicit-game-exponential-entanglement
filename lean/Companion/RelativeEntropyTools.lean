import Companion.BinaryQuantumStates

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

variable {a : Type*} [Fintype a] [DecidableEq a]

def midpointState (rho sigma : QIT.State a) : QIT.State a where
  matrix := (1/2:ℂ) • (rho.matrix+sigma.matrix)
  pos := by
    have h := (rho.pos.add sigma.pos).smul (show (0:ℝ)≤1/2 by norm_num)
    convert h using 1
    ext i j
    simp [Matrix.smul_apply,Complex.real_smul,mul_add]
  trace_eq_one := by
    rw [Matrix.trace_smul,Matrix.trace_add,rho.trace_eq_one,sigma.trace_eq_one]
    norm_num

theorem midpoint_self (rho : QIT.State a) : midpointState rho rho=rho := by
  apply QIT.State.ext
  ext i j
  simp only [midpointState,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]
  ring

theorem relativeEntropy_self (rho : QIT.State a) : rho.relativeEntropy rho=0 := by
  classical
  let hs := QIT.Matrix.Supports.refl rho.matrix
  rw [QIT.State.relativeEntropy_eq_coe_of_supports rho rho hs]
  let rhoC := QIT.psdSupportCompressedState rho rho.pos hs
  have hp : rhoC.matrix.PosDef := QIT.psdSupportCompress_self_posDef rho.matrix rho.pos
  have he := QIT.State.vonNeumann_eq_neg_trace_mul_psdLog_div_log_two rhoC hp
  change ((-rhoC.vonNeumann-((rhoC.matrix*QIT.State.psdLog rhoC.matrix hp).trace.re/Real.log 2):ℝ):EReal)=0
  have hz : -rhoC.vonNeumann-((rhoC.matrix*QIT.State.psdLog rhoC.matrix hp).trace.re/Real.log 2)=0 := by
    rw [he]
    ring
  simpa using congrArg (fun x : ℝ => (x:EReal)) hz

theorem relativeEntropy_finite_formula (rho sigma : QIT.State a)
    (hs : QIT.Matrix.Supports rho.matrix sigma.matrix) :
    QIT.State.relativeEntropyPSDReferenceTraceLogFinite rho sigma.matrix sigma.pos hs=
      -rho.vonNeumann-
        (rho.matrix*cfc (fun x : ℝ => if x=0 then 0 else Real.log x) sigma.matrix).trace.re/Real.log 2 := by
  classical
  have he := QIT.State.relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq rho sigma.pos hs
  have ht := QIT.State.relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero rho sigma.pos hs
  dsimp only [QIT.State.relativeEntropyPSDReferenceTraceLogFinite]
  rw [he]
  change -rho.vonNeumann-
    ((QIT.psdSupportCompress sigma.matrix sigma.pos rho.matrix*
      QIT.State.psdLog (QIT.psdSupportCompress sigma.matrix sigma.pos sigma.matrix)
        (QIT.psdSupportCompress_self_posDef sigma.matrix sigma.pos)).trace.re/Real.log 2)=_
  rw [ht]

theorem relativeEntropy_formula (rho sigma : QIT.State a)
    (hs : QIT.Matrix.Supports rho.matrix sigma.matrix) :
    rho.relativeEntropy sigma=
      ((-rho.vonNeumann-
        (rho.matrix*cfc (fun x : ℝ => if x=0 then 0 else Real.log x) sigma.matrix).trace.re/Real.log 2:ℝ):EReal) := by
  rw [QIT.State.relativeEntropy_eq_coe_of_supports rho sigma hs,relativeEntropy_finite_formula]

end
end Companion.Analytic.CountProof
