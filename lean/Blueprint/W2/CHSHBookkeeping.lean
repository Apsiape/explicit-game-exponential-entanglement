import Blueprint.RatesDefinitions
import Mathlib.Data.Nat.Choose.Cast

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

/-- Alice's actual reduced state, with its positive square root constructed. -/
def aliceState {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) : State a :=
  State.ofQuAIR {
    matrix := (psi.conjTranspose*psi).transpose
    pos := (Matrix.posSemidef_conjTranspose_mul_self psi).transpose
    trace_eq_one := by
      rw [Matrix.trace_transpose,CountProof.gram_trace,←hsNorm_sq,←hs_eq_hsNorm,hp]
      norm_num }

theorem aliceState_rho {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    (aliceState psi hp).rho=(psi.conjTranspose*psi).transpose := rfl

theorem pair_count (n : Nat) :
    (∑ i : Fin n, ∑ j : Fin n, if i<j then (1:ℝ) else 0)=(n.choose 2:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ]
    simp only [lt_self_iff_false,↓reduceIte,Fin.succ_pos,not_lt_of_ge (Fin.zero_le _),
      Fin.succ_lt_succ_iff,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      mul_one,zero_add,add_zero]
    rw [ih,Nat.choose_succ_succ,Nat.choose_one_right,Nat.cast_add]

theorem choose_two_cast (n : Nat) : (n.choose 2:ℝ)=(n:ℝ)*(n-1:Nat)/2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Nat.cast_choose_two, Nat.cast_sub (by omega : 1≤n+1),Nat.cast_one]

end
end Blueprint.W2
