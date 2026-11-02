/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in vendor/LeanQIT/LICENSE.
The root-multiset argument below is ported from QuAIR/Lean-QIT,
QIT/Information/Renyi/AlphaEntropyContinuity.lean, commit
8a931d4bda61ba503cfc0728704cfef5dedf2cff. The local port avoids importing
the unrelated Renyi development. Authors of the upstream argument: QuAIR Team.
-/
import Companion.QuAIRBridge
import Companion.CountPauliEmbedding

namespace Companion.Analytic
noncomputable section
open Matrix Polynomial
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 400000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private theorem roots_X_pow_entropy_zero (n : ℕ) :
    ((Polynomial.X ^ n : ℂ[X]).roots.map (fun z : ℂ => QIT.xlog2 z.re)).sum = 0 := by
  rw [Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton]
  simp [QIT.xlog2]

private theorem roots_entropy_eq_of_X_pow_mul_eq {P Q : ℂ[X]} {m n : ℕ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (h : Polynomial.X ^ m * P = Polynomial.X ^ n * Q) :
    (P.roots.map (fun z : ℂ => QIT.xlog2 z.re)).sum =
      (Q.roots.map (fun z : ℂ => QIT.xlog2 z.re)).sum := by
  have hXm : (Polynomial.X ^ m : ℂ[X]) ≠ 0 := by simp
  have hXn : (Polynomial.X ^ n : ℂ[X]) ≠ 0 := by simp
  have hleft_ne := mul_ne_zero hXm hP
  have hright_ne := mul_ne_zero hXn hQ
  have hroots := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne] at hroots
  have hsum := congrArg (fun s : Multiset ℂ => (s.map (fun z : ℂ => QIT.xlog2 z.re)).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add] at hsum
  rw [roots_X_pow_entropy_zero m,roots_X_pow_entropy_zero n] at hsum
  simpa using hsum

/-- A checked local port of QuAIR's rectangular-isometry entropy theorem. -/
theorem quair_entropy_isometry (ρ : QIT.State a) (σ : QIT.State b) (V : Matrix b a ℂ)
    (hV : V.conjTranspose*V=1) (hσ : σ.matrix=V*ρ.matrix*V.conjTranspose) :
    σ.vonNeumann=ρ.vonNeumann := by
  rw [QIT.State.vonNeumann_eq_neg_sum_eigenvalueMultiset,
    QIT.State.vonNeumann_eq_neg_sum_eigenvalueMultiset]
  congr 1
  have hpoly := Matrix.charpoly_mul_comm' (V*ρ.matrix) V.conjTranspose
  have hright : V.conjTranspose*(V*ρ.matrix)=ρ.matrix := by
    rw [← Matrix.mul_assoc,hV,Matrix.one_mul]
  rw [hright] at hpoly
  have hpolyσ : Polynomial.X ^ Fintype.card a * σ.matrix.charpoly =
      Polynomial.X ^ Fintype.card b * ρ.matrix.charpoly := by simpa [hσ] using hpoly
  have hroot := roots_entropy_eq_of_X_pow_mul_eq
    (Matrix.charpoly_monic σ.matrix).ne_zero (Matrix.charpoly_monic ρ.matrix).ne_zero hpolyσ
  rw [σ.pos.isHermitian.roots_charpoly_eq_eigenvalues,
    ρ.pos.isHermitian.roots_charpoly_eq_eigenvalues] at hroot
  simpa [QIT.eigenvalueMultiset,Multiset.map_map,Function.comp_def] using hroot

def isometryState (ρ : QIT.State a) (V : Matrix b a ℂ) (hV : V.conjTranspose*V=1) : QIT.State b where
  matrix := V*ρ.matrix*V.conjTranspose
  pos := ρ.pos.mul_mul_conjTranspose_same V
  trace_eq_one := by
    calc
      _=Matrix.trace (V.conjTranspose*(V*ρ.matrix)) := Matrix.trace_mul_comm _ _
      _=Matrix.trace ρ.matrix := by rw [← Matrix.mul_assoc,hV,Matrix.one_mul]
      _=1 := ρ.trace_eq_one

theorem isometryState_entropy (ρ : QIT.State a) (V : Matrix b a ℂ) (hV : V.conjTranspose*V=1) :
    (isometryState ρ V hV).vonNeumann=ρ.vonNeumann := quair_entropy_isometry ρ _ V hV rfl

def embeddedCountState {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i)) (s : State d) :
    QIT.State ((Fin M → Bool) × Fin d) :=
  isometryState s.toQuAIR (countEmbedding Z hZ) (countEmbedding_isometry Z hZ)

theorem countEmbedding_entropy {M d : Nat} (Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) :
    (embeddedCountState Z hZ s).vonNeumann=entropy s.rho := by
  rw [embeddedCountState,isometryState_entropy,entropy_eq_quair]

end
end Companion.Analytic
