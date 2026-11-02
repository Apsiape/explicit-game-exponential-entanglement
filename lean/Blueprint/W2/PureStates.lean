import Blueprint.RatesDefinitions

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def pureState {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    QIT.State (Fin a × Fin b) where
  matrix := pureDensity psi
  pos := Matrix.posSemidef_vecMulVec_self_star (fun i : Fin a × Fin b => psi i.2 i.1)
  trace_eq_one := by
    have hnorm : (∑ i, ∑ j, Complex.normSq (psi i j))=1 := by
      have hn : 0≤∑ i : Fin b, ∑ j : Fin a, Complex.normSq (psi i j) := by
        apply Finset.sum_nonneg
        intro i _
        apply Finset.sum_nonneg
        intro j _
        exact Complex.normSq_nonneg _
      have h := congrArg (fun x : ℝ => x^2) hp
      rw [hs,Real.sq_sqrt hn] at h
      norm_num at h
      exact h
    simp only [Matrix.trace,Matrix.diag_apply,pureDensity,Fintype.sum_prod_type,
      Complex.star_def,Complex.mul_conj]
    rw [Finset.sum_comm]
    exact_mod_cast hnorm

theorem pureState_matrix {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    (pureState psi hp).matrix=pureDensity psi := rfl

theorem pureState_decomposition {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    decomposition (pureState psi hp) (fun _ : Fin 1 => (1:ℝ)) (fun _ => psi) := by
  refine ⟨fun _ => zero_le_one,by simp,fun _ => hp,?_⟩
  simp [pureState]

end
end Blueprint.W2
