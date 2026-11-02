import Companion.OrthogonalReadout
import Companion.CountPauliRelations

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem symmetryProjection_anti_move (D C : Matrix a a ℂ) (ha : D*C=-(C*D)) (s : Bool) :
    D*symmetryProjection C s=symmetryProjection C (!s)*D := by
  cases s <;> simp [symmetryProjection,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,ha]

theorem jointProjection_intertwine (n : Nat) (C : Fin n → Matrix a a ℂ) (D : Matrix a a ℂ)
    (g h : Fin n → Bool)
    (hm : ∀ i, D*symmetryProjection (C i) (g i)=symmetryProjection (C i) (h i)*D) :
    D*jointProjection n C g=jointProjection n C h*D := by
  induction n with
  | zero => simp [jointProjection]
  | succ n ih =>
    rw [jointProjection,jointProjection,← Matrix.mul_assoc,
      ih (Fin.tail C) (Fin.tail g) (Fin.tail h) (fun i => hm i.succ),Matrix.mul_assoc,hm 0]
    simp only [Matrix.mul_assoc]

theorem jointProjection_flip (n : Nat) (C : Fin n → Matrix a a ℂ) (D : Matrix a a ℂ)
    (i : Fin n) (ha : D*C i=-(C i*D)) (hc : ∀ j, j≠i → Commute D (C j)) (g : Fin n → Bool) :
    D*jointProjection n C g=jointProjection n C (flip g i)*D := by
  apply jointProjection_intertwine
  intro j
  by_cases hj : j=i
  · subst j
    simpa [flip] using symmetryProjection_anti_move D (C i) ha (g i)
  · simp only [flip,Function.update_of_ne hj]
    exact (commute_symmetryProjection D (C j) (hc j hj) (g j)).eq

theorem jointProjection_flipped_norm {b : Type*} [Fintype b] [DecidableEq b]
    (n : Nat) (C : Fin n → Matrix a a ℂ) (D : Matrix a a ℂ)
    (hD : D.conjTranspose*D=1) (i : Fin n) (ha : D*C i=-(C i*D))
    (hc : ∀ j, j≠i → Commute D (C j)) (K : Matrix a b ℂ) (U : Matrix.unitaryGroup b ℂ)
    (g : Fin n → Bool) :
    hsNorm (jointProjection n C g*(D*K*(U:Matrix b b ℂ)))=
      hsNorm (jointProjection n C (flip g i)*K) := by
  have hm : jointProjection n C g*D=D*jointProjection n C (flip g i) := by
    simpa only [flip_flip] using (jointProjection_flip n C D i ha hc (flip g i)).symm
  have he : jointProjection n C g*(D*K*(U:Matrix b b ℂ))=
      D*(jointProjection n C (flip g i)*K)*(U:Matrix b b ℂ) := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hm]
    simp only [Matrix.mul_assoc]
  rw [he,hsNorm_unitary_right _ _ U.property.2,hsNorm_unitary_left _ _ hD]

end
end Companion.Analytic.CountProof
