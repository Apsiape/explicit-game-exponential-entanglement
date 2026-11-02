import Companion.BinaryPayoffOptimization

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem expectation_bob_trace {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (Q : Mat dB) :
    expectation psi P Q=(Q*(psi*P.transpose*psi.conjTranspose)).trace.re := by
  rw [expectation_trace,Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

def bobPayoff {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (j : Fin g.system.n) (b : Bool) : Mat dB :=
  ∑ i, ∑ a : Fin g.system.n → Bool,
    if j.val ∈ (g.system.equations[i.val]).vars ∧ a j=b then
      (g.pi i j:ℂ) • (s.psi*(s.alice i a).transpose*s.psi.conjTranspose) else 0

theorem bobPayoff_positive {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (j : Fin g.system.n) (b : Bool) : (bobPayoff s j b).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  apply Matrix.posSemidef_sum
  intro a _
  split
  · exact ((s.alice_positive i a).transpose.mul_mul_conjTranspose_same s.psi).smul
      (by exact_mod_cast g.pi_nonneg i j)
  · exact Matrix.PosSemidef.zero

theorem sum_bool_select {a : Type*} [Fintype a] (w : a → Bool) (f : Bool → a → ℝ) :
    (∑ b : Bool, ∑ x, if w x=b then f b x else 0)=∑ x, f (w x) x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : w x <;> simp [Fintype.sum_bool,hx]

theorem bobPayoff_trace {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (j : Fin g.system.n) (b : Bool) (Q : Mat dB) :
    (Q*bobPayoff s j b).trace.re=
      ∑ i, ∑ a : Fin g.system.n → Bool,
        if j.val ∈ (g.system.equations[i.val]).vars ∧ a j=b then
          g.pi i j*expectation s.psi (s.alice i a) Q else 0 := by
  simp only [bobPayoff,Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  split
  · rw [Matrix.mul_smul,Matrix.trace_smul,expectation_bob_trace]
    simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  · simp

theorem bobPayoff_total {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (j : Fin g.system.n) (Q : Bool → Mat dB) :
    (∑ b : Bool, (Q b*bobPayoff s j b).trace.re)=
      ∑ i, if j.val ∈ (g.system.equations[i.val]).vars then
        g.pi i j*(∑ a, expectation s.psi (s.alice i a) (Q (a j))) else 0 := by
  simp_rw [bobPayoff_trace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hj : j.val ∈ (g.system.equations[i.val]).vars
  · simp only [hj,true_and,↓reduceIte]
    have h := sum_bool_select (fun a : Fin g.system.n → Bool => a j)
      (fun b a => g.pi i j*expectation s.psi (s.alice i a) (Q b))
    rw [h,Finset.mul_sum]
  · simp [hj]

def strategyWithBob {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (Q : Fin g.system.n → Bool → Mat dB) (hp : ∀ j b, (Q j b).PosSemidef)
    (hc : ∀ j, Q j true+Q j false=1) : Strategy g dA dB :=
  { s with bob:=Q, bob_positive:=hp, bob_complete:=hc }

/-- The game payoff is linear in each of Bob's effects. The additive
constant consists exactly of unasked question pairs. -/
theorem win_bob_objective {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (Q : Fin g.system.n → Bool → Mat dB) (hp : ∀ j b, (Q j b).PosSemidef)
    (hc : ∀ j, Q j true+Q j false=1) :
    win (strategyWithBob s Q hp hc)=
      (∑ j, ∑ b : Bool, (Q j b*bobPayoff s j b).trace.re)+
        ∑ i, ∑ j, if j.val ∈ (g.system.equations[i.val]).vars then 0 else g.pi i j := by
  simp_rw [bobPayoff_total]
  rw [Finset.sum_comm (f:=fun j i => if j.val ∈ (g.system.equations[i.val]).vars then
    g.pi i j*(∑ a, expectation s.psi (s.alice i a) (Q j (a j))) else 0)]
  rw [← Finset.sum_add_distrib]
  unfold win
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val ∈ (g.system.equations[i.val]).vars <;>
    simp [pairWin,strategyWithBob,hj]

end
end Companion.Analytic.TransferProof
