import Companion.CubeConditionalEntropy

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

variable {a b z : Type*} [Fintype a] [DecidableEq a] [Fintype b] [Fintype z]

/-- Parseval's identity for a complete family of measurement operators.
Orthogonal projectors are a special case. -/
theorem measurement_parseval (P : z → Matrix a a ℂ)
    (hP : ∑ j, (P j).conjTranspose*P j=1) (A : Matrix a b ℂ) :
    (∑ j, hsNorm (P j*A)^2)=hsNorm A^2 := by
  simp_rw [hsNorm_sq,hsSquared_trace]
  have he : (∑ j, (P j*A).conjTranspose*(P j*A))=A.conjTranspose*A := by
    calc
      _=A.conjTranspose*(∑ j, (P j).conjTranspose*P j)*A := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
      _=_ := by rw [hP,Matrix.mul_one]
  have h := congrArg (fun X : Matrix b b ℂ => (Matrix.trace X).re) he
  simpa only [Matrix.trace_sum,Complex.re_sum] using h

/-- Measurement outcome norms cannot separate two factors by more than
their Hilbert--Schmidt distance. -/
theorem measurement_hellinger (P : z → Matrix a a ℂ)
    (hP : ∑ j, (P j).conjTranspose*P j=1) (K V : Matrix a b ℂ) :
    (∑ j, (hsNorm (P j*K)-hsNorm (P j*V))^2)≤hsNorm (K-V)^2 := by
  calc
    _≤∑ j, hsNorm (P j*(K-V))^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h : |hsNorm (P j*K)-hsNorm (P j*V)|≤hsNorm (P j*(K-V)) := by
        simpa only [hsNorm_eq_frobenius,Matrix.mul_sub] using abs_norm_sub_norm_le (P j*K) (P j*V)
      nlinarith [abs_le.mp h,hsNorm_nonneg (P j*(K-V))]
    _=_ := measurement_parseval P hP (K-V)

/-- The conditional-entropy estimate for any complete measurement whose
outcome norms on V are the flipped outcome norms on K. -/
theorem readout_conditional_bound {n : Nat} (P : (Fin n → Bool) → Matrix a a ℂ)
    (hP : ∑ g, (P g).conjTranspose*P g=1) (K V : Matrix a b ℂ) (hK : hsNorm K=1)
    (i : Fin n) (hflip : ∀ g, hsNorm (P g*V)=hsNorm (P (flip g i)*K))
    (e : ℝ) (he0 : 0≤e) (he : hsNorm (K-V)≤e) :
    1-e^2/(2*Real.log 2)≤cubeConditional (fun g => hsNorm (P g*K)^2) i := by
  have hp : ∀ g, 0≤hsNorm (P g*K)^2 := fun _ => sq_nonneg _
  have hpsum : ∑ g, hsNorm (P g*K)^2=1 := by rw [measurement_parseval P hP K,hK]; norm_num
  have h := cubeConditional_hellinger _ hp hpsum i
  simp only [Real.sqrt_sq (hsNorm_nonneg _)] at h
  have hh := measurement_hellinger P hP K V
  simp_rw [hflip] at hh
  have he2 : hsNorm (K-V)^2≤e^2 := pow_le_pow_left₀ (hsNorm_nonneg _) he 2
  have hd : 0<2*Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hb := div_le_div_of_nonneg_right (hh.trans he2) hd.le
  linarith

theorem readout_entropy_bound {n : Nat} (P : (Fin n → Bool) → Matrix a a ℂ)
    (hP : ∑ g, (P g).conjTranspose*P g=1) (K : Matrix a b ℂ) (hK : hsNorm K=1)
    (V : Fin n → Matrix a b ℂ)
    (hflip : ∀ i g, hsNorm (P g*V i)=hsNorm (P (flip g i)*K))
    (e : Fin n → ℝ) (he0 : ∀ i, 0≤e i) (he : ∀ i, hsNorm (K-V i)≤e i) :
    (∑ i, (1-(e i)^2/(2*Real.log 2)))≤cubeEntropy (fun g => hsNorm (P g*K)^2) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => readout_conditional_bound P hP K (V i) hK i (hflip i) (e i) (he0 i) (he i))
  apply hs.trans
  apply cubeEntropy_ge_sum_conditionals
  · intro g; exact sq_nonneg _
  · rw [measurement_parseval P hP K,hK]; norm_num

end
end Companion.Analytic.CountProof
