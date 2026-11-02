import Companion.AliceObservables

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem expectation_real_smul_right {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (Q : Mat dB) (c : ℝ) :
    expectation psi P ((c:ℂ) • Q)=c*expectation psi P Q := by
  simp only [expectation_bob_trace,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem expectation_neg_right {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (Q : Mat dB) : expectation psi P (-Q)= -expectation psi P Q := by
  simp only [expectation_bob_trace,Matrix.neg_mul,Matrix.trace_neg,Complex.neg_re]

theorem expectation_neg_left {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (Q : Mat dB) : expectation psi (-P) Q= -expectation psi P Q := by
  simp only [expectation_bob_trace,Matrix.transpose_neg,Matrix.mul_neg,Matrix.neg_mul,Matrix.trace_neg,Complex.neg_re]

theorem symmetryProjection_expectation {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (B : Mat dB) (b : Bool) :
    expectation psi P (CountProof.symmetryProjection B b)=
      (expectation psi P 1+(if b then -expectation psi P B else expectation psi P B))/2 := by
  have hh : ((1/2:ℝ):ℂ)=(1/2:ℂ) := by norm_num
  cases b <;> simp only [CountProof.symmetryProjection,Bool.false_eq_true,↓reduceIte]
  · rw [← hh,expectation_real_smul_right,expectation_add_right]
    ring
  · rw [← hh,expectation_real_smul_right,expectation_add_right,expectation_neg_right]
    ring

theorem outcomeObservable_expectation {n dA dB : Nat}
    (psi : Matrix (Fin dB) (Fin dA) ℂ) (P : QIT.ProjectiveMeasurement (Fin n → Bool) (Fin dA))
    (j : Fin n) (B : Mat dB) :
    expectation psi (outcomeObservable P j) B=
      ∑ a, if a j then -expectation psi (P.effects a) B else expectation psi (P.effects a) B := by
  rw [outcomeObservable,pvmFunction,expectation_sum_left]
  apply Finset.sum_congr rfl
  intro a _
  cases h : a j <;> simp [bitSign,h,expectation_neg_left]

theorem projective_pairWin_identity {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars)
    (P : QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin dA))
    (hA : ∀ a, s.alice i a=P.effects a) (B : Mat dB)
    (hBob : ∀ b, s.bob j b=CountProof.symmetryProjection B b) :
    pairWin s i j=(1+expectation s.psi (outcomeObservable P j) B)/2 := by
  rw [pairWin,if_pos hj]
  simp_rw [hA,hBob,symmetryProjection_expectation]
  rw [← Finset.sum_div,Finset.sum_add_distrib]
  have hn : (∑ a, expectation s.psi (P.effects a) 1)=1 := by
    rw [← expectation_sum_left,P.sum_eq_one,expectation_one_one s.psi s.normalized]
  rw [hn,← outcomeObservable_expectation]

/-- Exact squared-error/losing-probability identity for the prepared
projective measurements in the actual coefficient matrix convention. -/
theorem projective_consistency_squared {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars)
    (P : QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin dA))
    (hA : ∀ a, s.alice i a=P.effects a) (B : Mat dB) (hB : IsInvolution B)
    (hBob : ∀ b, s.bob j b=CountProof.symmetryProjection B b) :
    hsNorm (B*s.psi-s.psi*(outcomeObservable P j).transpose)^2=4*(1-pairWin s i j) := by
  have hAt : IsInvolution (outcomeObservable P j).transpose := by
    rw [outcomeObservable_transpose]
    exact outcomeObservable_involution _ j
  have hL : hsNorm (B*s.psi)=1 := by
    rw [hsNorm_unitary_left _ _ (CountProof.involution_unitary B hB).1]
    exact s.normalized
  have hR : hsNorm (s.psi*(outcomeObservable P j).transpose)=1 := by
    rw [hsNorm_unitary_right _ _ (CountProof.involution_unitary _ hAt).2]
    exact s.normalized
  have hc : ((B*s.psi).conjTranspose*(s.psi*(outcomeObservable P j).transpose)).trace.re=
      expectation s.psi (outcomeObservable P j) B := by
    rw [Matrix.conjTranspose_mul,hB.1,expectation_trace]
    simp only [Matrix.mul_assoc]
  have hd := CountProof.factor_distance_sq (B*s.psi) (s.psi*(outcomeObservable P j).transpose)
  rw [hL,hR,hc] at hd
  have hw := projective_pairWin_identity s i j hj P hA B hBob
  nlinarith

theorem projective_consistency_bound {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (eps : ℝ)
    (heps : 0≤eps) (hw : 1-eps≤win s)
    (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars)
    (P : QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin dA))
    (hA : ∀ a, s.alice i a=P.effects a) (B : Mat dB) (hB : IsInvolution B)
    (hBob : ∀ b, s.bob j b=CountProof.symmetryProjection B b) :
    hsNorm (B*s.psi-s.psi*(outcomeObservable P j).transpose)≤theta g eps := by
  have h := projective_consistency_squared s i j hj P hA B hB hBob
  have hl := pair_loss_le s eps hw i j hj
  have ht : (theta g eps)^2=4*(eps/g.piMin) := by
    unfold theta
    rw [mul_pow,Real.sq_sqrt (div_nonneg heps g.piMin_pos.le)]
    ring
  nlinarith [hsNorm_nonneg (B*s.psi-s.psi*(outcomeObservable P j).transpose),theta_nonneg g eps]

theorem projective_state_commutator {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (hpd : (s.psi*s.psi.conjTranspose).PosDef) (eps : ℝ) (heps : 0≤eps) (hw : 1-eps≤win s)
    (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars)
    (P : QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin dA))
    (hA : ∀ a, s.alice i a=P.effects a) (B : Mat dB) (hB : IsInvolution B)
    (hBob : ∀ b, s.bob j b=CountProof.symmetryProjection B b) :
    hsNorm (comm B (QIT.psdSqrt (s.psi*s.psi.conjTranspose)))≤Real.sqrt 2*theta g eps := by
  have hAh : ((outcomeObservable P j).transpose).IsHermitian := by
    rw [outcomeObservable_transpose]
    exact (outcomeObservable_involution _ j).1
  have h := rectangular_consistency s.psi hpd (outcomeObservable P j).transpose B hAh hB.1
  exact h.trans (mul_le_mul_of_nonneg_left
    (projective_consistency_bound s eps heps hw i j hj P hA B hB hBob) (Real.sqrt_nonneg 2))

end
end Companion.Analytic.TransferProof
