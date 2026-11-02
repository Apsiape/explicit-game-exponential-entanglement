import Blueprint.W2.RectangularConsistency
import Blueprint.W2.CHSHExact

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

theorem hs_transpose {a b : Nat} (P : Matrix (Fin a) (Fin b) ℂ) : hs P.transpose=hs P := by
  unfold hs
  congr 1
  exact Finset.sum_comm

theorem rectangular_sub_square {a b : Nat} (P Q : Matrix (Fin a) (Fin b) ℂ) :
    hs (P-Q)^2=hs P^2+hs Q^2-2*(P.conjTranspose*Q).trace.re := by
  have hh : (Q.conjTranspose*P).trace.re=(P.conjTranspose*Q).trace.re := by
    have he : Q.conjTranspose*P=(P.conjTranspose*Q).conjTranspose := by simp
    rw [he,Matrix.trace_conjTranspose]
    simp
  simp only [hs_eq_hsNorm,hsNorm_sq,hsSquared_trace,Matrix.conjTranspose_sub,
    Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,hh]
  ring

theorem expectation_real_smul {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Mat a) (B : Mat b) (r : ℝ) :
    expectation psi A ((r:ℂ) • B)=r*expectation psi A B := by
  simp [TransferProof.expectation_trace,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.trace_smul,Complex.mul_re]

theorem pair_sum_squares {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1)
    (A A' : Mat a) (B B' : Mat b) (hA : IsInvolution A) (hA' : IsInvolution A')
    (hB : IsInvolution B) (hB' : IsInvolution B') :
    let T := chshPlus B B'
    let T' := chshPlus B (-B')
    hs (T*psi-psi*A.transpose)^2+hs (T'*psi-psi*A'.transpose)^2=
      Real.sqrt 2*(2*Real.sqrt 2-(expectation psi A (B+B')+expectation psi A' (B-B'))) := by
  dsimp only
  let T := chshPlus B B'
  let T' := chshPlus B (-B')
  have hT : T.IsHermitian := by simp [T,chshPlus,Matrix.IsHermitian,Matrix.conjTranspose_smul,hB.1,hB'.1]
  have hT' : T'.IsHermitian := by simp [T',chshPlus,Matrix.IsHermitian,Matrix.conjTranspose_smul,hB.1,hB'.1]
  have hcoef : (((1/Real.sqrt 2:ℝ):ℂ))*(((1/Real.sqrt 2:ℝ):ℂ))*(2:ℂ)=1 := by
    have hh : (1/Real.sqrt 2:ℝ)*(1/Real.sqrt 2)*2=1 := by
      field_simp
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    exact_mod_cast hh
  have hTT : T*T+T'*T'=(2:ℂ) • (1:Mat b) := by
    have he : (B+B')*(B+B')+(B-B')*(B-B')=(4:ℂ) • (1:Mat b) := by
      calc
        _=(B*B+B*B)+(B'*B'+B'*B') := by noncomm_ring
        _=_ := by rw [hB.2,hB'.2]; module
    simp only [T,T',chshPlus,←sub_eq_add_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [←smul_add,he,smul_smul]
    have hc : (((1/Real.sqrt 2:ℝ):ℂ))*(((1/Real.sqrt 2:ℝ):ℂ))*(4:ℂ)=2 := by linear_combination 2*hcoef
    rw [hc]
  have hnorm : hs (T*psi)^2+hs (T'*psi)^2=2 := by
    simp only [hs_eq_hsNorm,hsNorm_sq,hsSquared_trace,Matrix.conjTranspose_mul,hT.eq,hT'.eq]
    rw [←Complex.add_re,←Matrix.trace_add]
    have he : psi.conjTranspose*T*(T*psi)+psi.conjTranspose*T'*(T'*psi)=
        (2:ℂ) • (psi.conjTranspose*psi) := by
      calc
        _=psi.conjTranspose*(T*T+T'*T')*psi := by simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
        _=_ := by rw [hTT]; simp [Matrix.mul_smul,Matrix.smul_mul]
    rw [he,Matrix.trace_smul]
    have hh : (psi.conjTranspose*psi).trace.re=1 := by
      rw [←hsSquared_trace,←hsNorm_sq,←hs_eq_hsNorm,hp]; norm_num
    norm_num [Complex.mul_re,hh]
  have huA := CountProof.involution_unitary _ (ReturnProof.transpose_involution _ hA)
  have huA' := CountProof.involution_unitary _ (ReturnProof.transpose_involution _ hA')
  have hnormA : hs (psi*A.transpose)=1 := by
    rw [hs_eq_hsNorm,hsNorm_unitary_right _ _ huA.2]; exact hp
  have hnormA' : hs (psi*A'.transpose)=1 := by
    rw [hs_eq_hsNorm,hsNorm_unitary_right _ _ huA'.2]; exact hp
  have cross (D : Mat a) (S : Mat b) (hS : S.IsHermitian) :
      ((S*psi).conjTranspose*(psi*D.transpose)).trace.re=expectation psi D S := by
    rw [Matrix.conjTranspose_mul,hS.eq,TransferProof.expectation_trace]
    simp only [Matrix.mul_assoc]
  rw [rectangular_sub_square,rectangular_sub_square,hnormA,hnormA',cross A T hT,cross A' T' hT']
  have hscale : 2*(1/Real.sqrt 2:ℝ)=Real.sqrt 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hsT : expectation psi A T=(1/Real.sqrt 2)*expectation psi A (B+B') :=
    expectation_real_smul psi A (B+B') (1/Real.sqrt 2)
  have hsT' : expectation psi A' T'=(1/Real.sqrt 2)*expectation psi A' (B-B') := by
    simpa only [T',chshPlus,sub_eq_add_neg] using expectation_real_smul psi A' (B+ -B') (1/Real.sqrt 2)
  rw [hsT,hsT']
  dsimp only [T,T'] at hnorm
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
    congrArg (fun r : ℝ => r*(expectation psi A (B+B')+expectation psi A' (B-B'))) hscale]

end
end Blueprint.W2
