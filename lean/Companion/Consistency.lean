import Companion.HilbertSchmidt
import Mathlib.Tactic.Ring
set_option maxHeartbeats 300000

namespace Companion.Analytic
noncomputable section
open scoped BigOperators ComplexOrder

private theorem scalar_consistency (a b : ℂ) (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    Complex.normSq (b*(y:ℂ)-(x:ℂ)*a) + Complex.normSq (b*(x:ℂ)-(y:ℂ)*a) ≥
      Complex.normSq (b*(y:ℂ)-(x:ℂ)*b) := by
  have identity :
      Complex.normSq (b*(y:ℂ)-(x:ℂ)*a) + Complex.normSq (b*(x:ℂ)-(y:ℂ)*a) -
        Complex.normSq (b*(y:ℂ)-(x:ℂ)*b) =
      (x-y)^2*Complex.normSq a + 2*x*y*Complex.normSq (a-b) := by
    simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.sub_re,
      Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have hn : 0≤(x-y)^2*Complex.normSq a + 2*x*y*Complex.normSq (a-b) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (mul_nonneg (by positivity) (Complex.normSq_nonneg _))
  linarith

/-- Entrywise proof of the state-consistency estimate in an eigenbasis.
Neither approximate Pauli relations nor a counting theorem are hypotheses. -/
theorem diagonal_consistency {d : Nat} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (lambda : Fin d → ℝ) (hlambda : ∀ i, 0≤lambda i) :
    hsSquared (comm B (Matrix.diagonal (fun i => (lambda i:ℂ)))) ≤
      2*hsSquared (B*Matrix.diagonal (fun i => (lambda i:ℂ)) -
        Matrix.diagonal (fun i => (lambda i:ℂ))*A) := by
  let E : Fin d → Fin d → ℝ := fun i j =>
    Complex.normSq (B i j*(lambda j:ℂ)-(lambda i:ℂ)*A i j)
  have hentry (i j : Fin d) :
      Complex.normSq (B i j*(lambda j:ℂ)-(lambda i:ℂ)*B i j) ≤ E i j+E j i := by
    have h := scalar_consistency (A i j) (B i j) (lambda i) (lambda j) (hlambda i) (hlambda j)
    have ha : A j i=star (A i j) := by
      simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.eq j) i |>.symm
    have hb : B j i=star (B i j) := by
      simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hB.eq j) i |>.symm
    have he : E j i=Complex.normSq (B i j*(lambda i:ℂ)-(lambda j:ℂ)*A i j) := by
      simp only [E,ha,hb]
      rw [show star (B i j)*(lambda i:ℂ)-(lambda j:ℂ)*star (A i j)=
        star (B i j*(lambda i:ℂ)-(lambda j:ℂ)*A i j) by simp]
      exact Complex.normSq_conj _
    simpa only [he,E] using h
  simp only [hsSquared,comm,Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul]
  calc
    _ ≤ ∑ i, ∑ j, (E i j+E j i) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = 2*∑ i, ∑ j, E i j := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => E j i)]
      ring

/-- The finite-dimensional consistency lemma: an approximately matching
Hermitian operator on the other purification register forces a small
commutator with the positive square-root factor. -/
theorem consistency_squared {d : Nat} (A B xi : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hxi : xi.PosSemidef) :
    (hsNorm (comm B xi))^2 ≤ 2*(hsNorm (B*xi-xi*A))^2 := by
  let U := hxi.isHermitian.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ (Mat d) (star U)
  let lambda := hxi.isHermitian.eigenvalues
  have hD : C xi=Matrix.diagonal (fun i => (lambda i:ℂ)) :=
    hxi.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hHerm (T : Mat d) (hT : T.IsHermitian) : (C T).IsHermitian := by
    dsimp only [C]
    rw [Unitary.conjStarAlgAut_star_apply]
    change ((U:Mat d).conjTranspose*T*(U:Mat d)).IsHermitian
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hT
  have hnorm (T : Mat d) : hsSquared (C T)=hsSquared T := by
    have hn : hsNorm (C T)=hsNorm T := by
      dsimp only [C]
      rw [Unitary.conjStarAlgAut_star_apply]
      change hsNorm ((U:Mat d).conjTranspose*T*(U:Mat d))=hsNorm T
      rw [hsNorm_unitary_right (U:Mat d) _ U.property.2]
      apply hsNorm_unitary_left
      simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using U.property.2
    calc
      _ = (hsNorm (C T))^2 := (hsNorm_sq _).symm
      _ = (hsNorm T)^2 := congrArg (fun x : ℝ => x^2) hn
      _ = _ := hsNorm_sq _
  have h := diagonal_consistency (C A) (C B) (hHerm A hA) (hHerm B hB) lambda
    (fun i => hxi.eigenvalues_nonneg i)
  have hc : comm (C B) (Matrix.diagonal (fun i => (lambda i:ℂ)))=C (comm B xi) := by
    simp only [comm,map_sub,map_mul,hD]
  have he : C B*Matrix.diagonal (fun i => (lambda i:ℂ))-
      Matrix.diagonal (fun i => (lambda i:ℂ))*C A=C (B*xi-xi*A) := by
    simp only [map_sub,map_mul,hD]
  rw [hc,he,hnorm,hnorm] at h
  simpa only [hsNorm_sq] using h

theorem consistency {d : Nat} (A B xi : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hxi : xi.PosSemidef) :
    hsNorm (comm B xi) ≤ Real.sqrt 2*hsNorm (B*xi-xi*A) := by
  have h := consistency_squared A B xi hA hB hxi
  have hs : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have hn := hsNorm_nonneg (B*xi-xi*A)
  have hc := hsNorm_nonneg (comm B xi)
  have h2 := Real.sqrt_nonneg (2:ℝ)
  apply (sq_le_sq₀ hc (mul_nonneg h2 hn)).mp
  simpa only [mul_pow,hs] using h

end
end Companion.Analytic
