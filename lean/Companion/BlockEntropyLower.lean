import Companion.ReadoutHellinger

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

variable {a z : Type*} [Fintype a] [DecidableEq a] [Fintype z] [DecidableEq z]

/-- A normalized block; a zero block can use any density state because
its weight is zero. -/
def normalizedBlock (B : Matrix a a ℂ) (hB : B.PosSemidef) (fallback : QIT.State a) : QIT.State a :=
  if h : B.trace.re=0 then fallback else QIT.State.normalizePSD B hB h

theorem normalizedBlock_scale (B : Matrix a a ℂ) (hB : B.PosSemidef) (fallback : QIT.State a) :
    (B.trace.re:ℂ) • (normalizedBlock B hB fallback).matrix=B := by
  by_cases h : B.trace.re=0
  · have ht : B.trace=0 := Complex.ext h (hB.trace_nonneg.2.symm)
    have hz := hB.trace_eq_zero_iff.mp ht
    simp [hz]
  · have he : B.trace.re • (normalizedBlock B hB fallback).matrix=B := by
      rw [normalizedBlock,dite_eq_right h,QIT.State.normalizePSD_matrix,smul_smul,mul_inv_cancel₀ h,one_smul]
    convert he using 1

theorem negMulLog_bits (x : ℝ) : Real.negMulLog x/Real.log 2= -QIT.xlog2 x := by
  by_cases hx : x=0
  · simp [hx,Real.negMulLog,QIT.xlog2]
  · simp [Real.negMulLog,QIT.xlog2,QIT.log2,hx,div_eq_mul_inv,mul_assoc]

/-- The entropy of a block-diagonal density state dominates the Shannon
entropy of its block weights, including blocks of zero weight. -/
theorem block_entropy_lower (rho : QIT.State (a × z)) (B : z → Matrix a a ℂ)
    (hB : ∀ j, (B j).PosSemidef) (hrho : rho.matrix=Matrix.blockDiagonal B) :
    (∑ j, Real.negMulLog (B j).trace.re)/Real.log 2≤rho.vonNeumann := by
  let sigma := fun j => normalizedBlock (B j) (hB j) rho.marginalA
  have hm : rho.matrix=Matrix.blockDiagonal (fun j => ((B j).trace.re:ℂ) • (sigma j).matrix) := by
    simpa only [sigma,normalizedBlock_scale] using hrho
  have he := QIT.State.vonNeumann_eq_shannon_add_average_of_blockDiagonal rho
    (fun j => (B j).trace.re) sigma (fun j => (hB j).trace_nonneg.1) hm
  have hn : 0≤∑ j, (B j).trace.re*(sigma j).vonNeumann :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hB j).trace_nonneg.1 ((sigma j).vonNeumann_nonneg))
  rw [he,Finset.sum_div]
  simp_rw [negMulLog_bits]
  rw [Finset.sum_neg_distrib]
  linarith

end
end Companion.Analytic.CountProof
