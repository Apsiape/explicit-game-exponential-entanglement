import Companion.FlatFourier

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

/-- The columns of U form an orthonormal basis with zero H diagonal.
The construction diagonalizes H and then uses a flat Fourier unitary. -/
theorem zero_diagonal_basis (n : Nat) (H : Mat n) (hH : H.IsHermitian) (htr : Matrix.trace H=0) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, ∀ j, ((U:Mat n).conjTranspose*H*(U:Mat n)) j j=0 := by
  cases n with
  | zero => exact ⟨1,fun j => j.elim0⟩
  | succ n =>
    let E := hH.eigenvectorUnitary
    let F := flatUnitary (n+1)
    refine ⟨E*F,fun j => ?_⟩
    have hd : (E:Mat (n+1)).conjTranspose*H*(E:Mat (n+1))=
        Matrix.diagonal (fun i => (hH.eigenvalues i:ℂ)) := by
      have hh := hH.conjStarAlgAut_star_eigenvectorUnitary
      simp only [Unitary.conjStarAlgAut_star_apply] at hh
      change (E:Mat (n+1)).conjTranspose*H*(E:Mat (n+1))=
        Matrix.diagonal (fun i => (hH.eigenvalues i:ℂ)) at hh
      exact hh
    have he : ((E*F:Matrix.unitaryGroup (Fin (n+1)) ℂ):Mat (n+1)).conjTranspose*H*
        ((E*F:Matrix.unitaryGroup (Fin (n+1)) ℂ):Mat (n+1))=
        (flatMatrix (n+1)).conjTranspose*((E:Mat (n+1)).conjTranspose*H*(E:Mat (n+1)))*flatMatrix (n+1) := by
      simp only [Submonoid.coe_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc,F,flatUnitary]
    have hsum : (∑ i, (hH.eigenvalues i:ℂ))=0 := by
      have ht := hH.trace_eq_sum_eigenvalues
      change Matrix.trace H=(∑ i, (hH.eigenvalues i:ℂ)) at ht
      exact ht.symm.trans htr
    rw [he,hd,flat_diagonal,hsum,mul_zero]

theorem gram_trace {a b : Type*} [Fintype a] [Fintype b] (L : Matrix a b ℂ) :
    Matrix.trace (L.conjTranspose*L)=(hsSquared L:ℂ) := by
  calc
    _=∑ j, ∑ i, (Complex.normSq (L i j):ℂ) := by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Complex.star_def,← Complex.normSq_eq_conj_mul_self]
    _=_ := by
      simp only [hsSquared,Complex.ofReal_sum]
      exact Finset.sum_comm

def columnVector {a : Type*} [Fintype a] {n : Nat} (L : Matrix a (Fin n) ℂ) (j : Fin n) :
    EuclideanSpace ℂ a := WithLp.toLp 2 (fun i => L i j)

theorem columnVector_norm_sq {a : Type*} [Fintype a] {n : Nat}
    (L : Matrix a (Fin n) ℂ) (j : Fin n) :
    ‖columnVector L j‖^2=((L.conjTranspose*L) j j).re := by
  have he : (L.conjTranspose*L) j j=∑ i, (Complex.normSq (L i j):ℂ) := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self]
  rw [he,Complex.re_sum,EuclideanSpace.norm_sq_eq]
  simp only [columnVector,Complex.ofReal_re,Complex.normSq_eq_norm_sq]

/-- Equal HS norms admit a single orthonormal domain basis in which every
corresponding pair of columns has equal norm. In particular this applies to
the two unit-HS factors in the Jensen--Shannon argument. -/
theorem equal_column_norms {a : Type*} [Fintype a] (n : Nat)
    (L L' : Matrix a (Fin n) ℂ) (hn : hsNorm L=hsNorm L') :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, ∀ j,
      ‖columnVector (L*(U:Mat n)) j‖=‖columnVector (L'*(U:Mat n)) j‖ := by
  let H := L.conjTranspose*L-L'.conjTranspose*L'
  have hH : H.IsHermitian := by
    change H.conjTranspose=H
    simp [H,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul]
  have hsq : hsSquared L=hsSquared L' := by rw [← hsNorm_sq,← hsNorm_sq,hn]
  have ht : Matrix.trace H=0 := by
    dsimp only [H]
    rw [Matrix.trace_sub,gram_trace,gram_trace,hsq,sub_self]
  obtain ⟨U,hU⟩ := zero_diagonal_basis n H hH ht
  refine ⟨U,fun j => ?_⟩
  have hd := hU j
  have he : (U:Mat n).conjTranspose*H*(U:Mat n)=
      (L*(U:Mat n)).conjTranspose*(L*(U:Mat n))-
        (L'*(U:Mat n)).conjTranspose*(L'*(U:Mat n)) := by
    simp only [H,Matrix.mul_sub,Matrix.sub_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he] at hd
  have hr := congrArg Complex.re hd
  simp only [Matrix.sub_apply,Complex.sub_re,Complex.zero_re,← columnVector_norm_sq] at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_eq_zero.mp hr)

end
end Companion.Analytic.CountProof
