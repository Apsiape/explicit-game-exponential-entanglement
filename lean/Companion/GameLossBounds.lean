import Companion.AliceProjectiveStrategy

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem psd_trace_mul_nonneg {d : Nat} (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0≤(A*B).trace.re := by
  let S := QIT.psdSqrt A
  have hS : S.conjTranspose=S := QIT.psdSqrt_isHermitian A
  have hSS : S*S=A := QIT.psdSqrt_mul_self_of_posSemidef hA
  have hp : (S*B*S).PosSemidef := by
    simpa only [hS] using hB.mul_mul_conjTranspose_same S
  have he : (A*B).trace=(S*B*S).trace := by
    calc
      _=((S*S)*B).trace := by rw [hSS]
      _=_ := (Matrix.trace_mul_cycle S B S).symm
  rw [he]
  exact hp.trace_nonneg.1

theorem expectation_nonneg {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (Q : Mat dB) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0≤expectation psi P Q := by
  rw [expectation_bob_trace]
  exact psd_trace_mul_nonneg Q _ hQ (hP.transpose.mul_mul_conjTranspose_same psi)

theorem expectation_add_right {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (Q R : Mat dB) :
    expectation psi P (Q+R)=expectation psi P Q+expectation psi P R := by
  simp only [expectation_bob_trace,Matrix.add_mul,Matrix.trace_add,Complex.add_re]

theorem expectation_sum_left {dA dB : Nat} {y : Type*} [Fintype y]
    (psi : Matrix (Fin dB) (Fin dA) ℂ) (P : y → Mat dA) (Q : Mat dB) :
    expectation psi (∑ a, P a) Q=∑ a, expectation psi (P a) Q := by
  have ht : (∑ a, P a).transpose=∑ a, (P a).transpose := by
    ext i j
    simp only [Matrix.transpose_apply,Matrix.sum_apply]
  simp only [expectation_bob_trace,ht,Matrix.mul_sum,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum]

theorem expectation_one_one {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ) (hn : hsNorm psi=1) :
    expectation psi 1 1=1 := by
  rw [expectation_trace,Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one,← hsSquared_trace,← hsNorm_sq,hn]
  norm_num

theorem pairWin_nonneg {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) : 0≤pairWin s i j := by
  unfold pairWin
  split
  · exact Finset.sum_nonneg (fun a _ => expectation_nonneg s.psi _ _ (s.alice_positive i a) (s.bob_positive j (a j)))
  · norm_num

theorem pairWin_le_one {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) : pairWin s i j≤1 := by
  unfold pairWin
  split
  · have hb (a : Fin g.system.n → Bool) : s.bob j (a j)+s.bob j (!(a j))=1 := by
      cases h : a j <;> simpa [h,add_comm] using s.bob_complete j
    have he : (∑ a, expectation s.psi (s.alice i a) (s.bob j (a j)))+
        (∑ a, expectation s.psi (s.alice i a) (s.bob j (!(a j))))=1 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [← expectation_add_right,hb]
      rw [← expectation_sum_left,s.alice_complete i,expectation_one_one s.psi s.normalized]
    have hn : 0≤∑ a, expectation s.psi (s.alice i a) (s.bob j (!(a j))) :=
      Finset.sum_nonneg (fun a _ => expectation_nonneg s.psi _ _ (s.alice_positive i a) (s.bob_positive j _))
    linarith
  · exact le_rfl

theorem weighted_loss_sum {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    (∑ i, ∑ j, g.pi i j*(1-pairWin s i j))=1-win s := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
  rw [g.pi_normalized]
  rfl

/-- Individual loss on each asked pair is bounded using exactly piMin. -/
theorem pair_loss_le {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (eps : ℝ)
    (hw : 1-eps≤win s) (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars) :
    1-pairWin s i j≤eps/g.piMin := by
  have hn : ∀ i j, 0≤g.pi i j*(1-pairWin s i j) :=
    fun i j => mul_nonneg (g.pi_nonneg i j) (sub_nonneg.mpr (pairWin_le_one s i j))
  have h1 : g.pi i j*(1-pairWin s i j)≤∑ j', g.pi i j'*(1-pairWin s i j') :=
    Finset.single_le_sum (fun j' _ => hn i j') (Finset.mem_univ j)
  have h2 : (∑ j', g.pi i j'*(1-pairWin s i j'))≤∑ i', ∑ j', g.pi i' j'*(1-pairWin s i' j') :=
    Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => hn i' j')) (Finset.mem_univ i)
  have hmin := mul_le_mul_of_nonneg_right (g.piMin_lower i j hj) (sub_nonneg.mpr (pairWin_le_one s i j))
  have ht := (hmin.trans h1).trans h2
  rw [weighted_loss_sum] at ht
  apply (le_div_iff₀ g.piMin_pos).mpr
  nlinarith

end
end Companion.Analytic.TransferProof
