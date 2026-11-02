import Companion.CountEmbedding
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace Companion.Analytic
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 500000

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def normalizedBlocks (A : β → Matrix α γ ℂ) : Matrix (β × α) γ ℂ :=
  fun ba j => (uniformCoefficient β:ℂ)*A ba.1 ba.2 j

theorem normalizedBlocks_mul {δ : Type*} (A : β → Matrix α γ ℂ) (B : Matrix γ δ ℂ) :
    normalizedBlocks A*B=normalizedBlocks (fun b => A b*B) := by
  ext ⟨b,a⟩ j
  simp only [Matrix.mul_apply,normalizedBlocks,Finset.mul_sum,mul_assoc]

theorem normalizedBlocks_hs_sq [Nonempty β] (A : β → Matrix α γ ℂ) :
    hsNorm (normalizedBlocks A)^2=(∑ b, hsNorm (A b)^2)/(Fintype.card β:ℝ) := by
  have hn : (Fintype.card β:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : uniformCoefficient β*uniformCoefficient β=1/(Fintype.card β:ℝ) :=
    (eq_div_iff hn).mpr (uniformCoefficient_square β)
  simp only [hsNorm_sq,hsSquared,normalizedBlocks,Fintype.sum_prod_type,Complex.normSq_mul,
    Complex.normSq_ofReal,← Finset.mul_sum]
  rw [hc]
  ring

theorem flip_flip {M : Nat} (g : Fin M → Bool) (i : Fin M) : flip (flip g i) i=g := by
  funext j
  by_cases h : j=i
  · subst j; simp [flip]
  · simp [flip,Function.update_of_ne h]

theorem flip_commute {M : Nat} (g : Fin M → Bool) (i j : Fin M) :
    flip (flip g i) j=flip (flip g j) i := by
  by_cases hij : i=j
  · subst j; rfl
  funext k
  by_cases hki : k=i
  · subst k; simp [flip,Function.update_of_ne hij,Function.update_of_ne (Ne.symm hij)]
  · by_cases hkj : k=j
    · subst k; simp [flip,Function.update_of_ne hij,Function.update_of_ne (Ne.symm hij)]
    · simp [flip,Function.update_of_ne hki,Function.update_of_ne hkj]

def cubeIndexFlip {M d : Nat} (i : Fin M) : Equiv.Perm ((Fin M → Bool) × Fin d) where
  toFun ga := (flip ga.1 i,ga.2)
  invFun ga := (flip ga.1 i,ga.2)
  left_inv ga := by simp [flip_flip]
  right_inv ga := by simp [flip_flip]

theorem cubeIndexFlip_inv {M d : Nat} (i : Fin M) :
    (cubeIndexFlip (d:=d) i)⁻¹=cubeIndexFlip i := by ext ga <;> rfl

theorem cubeIndexFlip_square {M d : Nat} (i : Fin M) :
    cubeIndexFlip (d:=d) i*cubeIndexFlip i=1 := by
  apply Equiv.ext
  rintro ⟨g,a⟩
  change (flip (flip g i) i,a)=(g,a)
  rw [flip_flip]

def cubeShift {M d : Nat} (i : Fin M) : Matrix ((Fin M → Bool) × Fin d) ((Fin M → Bool) × Fin d) ℂ :=
  (cubeIndexFlip (d:=d) i).permMatrix ℂ

theorem cubeShift_involution {M d : Nat} (i : Fin M) :
    (cubeShift (d:=d) i).conjTranspose=cubeShift i ∧ cubeShift (d:=d) i*cubeShift i=1 := by
  constructor
  · simp only [cubeShift,Matrix.conjTranspose_permMatrix,cubeIndexFlip_inv]
  · rw [cubeShift,← Matrix.permMatrix_mul,cubeIndexFlip_square,Matrix.permMatrix_one]

theorem cubeShift_commute {M d : Nat} (i j : Fin M) :
    Commute (cubeShift (d:=d) i) (cubeShift j) := by
  have he : cubeIndexFlip (d:=d) i*cubeIndexFlip j=cubeIndexFlip j*cubeIndexFlip i := by
    apply Equiv.ext
    rintro ⟨g,a⟩
    change (flip (flip g j) i,a)=(flip (flip g i) j,a)
    rw [flip_commute]
  change cubeShift i*cubeShift j=cubeShift j*cubeShift i
  simp only [cubeShift,← Matrix.permMatrix_mul,he]

theorem cubeShift_mul {M d : Nat} {δ : Type*} (i : Fin M)
    (A : Matrix ((Fin M → Bool) × Fin d) δ ℂ) (g : Fin M → Bool) (a : Fin d) (b : δ) :
    (cubeShift (d:=d) i*A) (g,a) b=A (flip g i,a) b := by
  rw [cubeShift,Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_mul]
  rfl

def bitSign {M : Nat} (g : Fin M → Bool) (i : Fin M) : ℂ := if g i then -1 else 1

def cubeTwist {M d : Nat} (X : Mat d) (i : Fin M) :
    Matrix ((Fin M → Bool) × Fin d) ((Fin M → Bool) × Fin d) ℂ :=
  fun ga hb => if ga.1=hb.1 then bitSign ga.1 i*X ga.2 hb.2 else 0

theorem cubeTwist_mul {M d : Nat} {δ : Type*} (X : Mat d) (i : Fin M)
    (A : Matrix ((Fin M → Bool) × Fin d) δ ℂ) (g : Fin M → Bool) (a : Fin d) (b : δ) :
    (cubeTwist X i*A) (g,a) b=bitSign g i*(∑ c, X a c*A (g,c) b) := by
  classical
  simp [cubeTwist,Matrix.mul_apply,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem countEmbedding_mul {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (A : Mat d) (g : Fin M → Bool) (a b : Fin d) :
    (countEmbedding Z hZ*A) (g,a) b=
      (uniformCoefficient (Fin M → Bool):ℂ)*(orderedZ Z g*A) a b := by
  simp only [Matrix.mul_apply,countEmbedding,uniformEmbedding,orderedZUnitary_matrix]
  rw [Finset.mul_sum]
  simp only [mul_assoc]

theorem cubeTwist_normalizedBlocks {M d : Nat} {δ : Type*} (X : Mat d) (i : Fin M)
    (A : (Fin M → Bool) → Matrix (Fin d) δ ℂ) :
    cubeTwist X i*normalizedBlocks A=normalizedBlocks (fun g => bitSign g i • (X*A g)) := by
  ext ⟨g,a⟩ b
  rw [cubeTwist_mul]
  simp only [normalizedBlocks,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem countEmbedding_right {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (A : Mat d) : countEmbedding Z hZ*A=normalizedBlocks (fun g => orderedZ Z g*A) := by
  ext ⟨g,a⟩ b
  exact countEmbedding_mul Z hZ A g a b

theorem cubeShift_embedding {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (i : Fin M) : cubeShift i*countEmbedding Z hZ=normalizedBlocks (fun g => orderedZ Z (flip g i)) := by
  ext ⟨g,a⟩ b
  rw [cubeShift_mul]
  simp only [countEmbedding,uniformEmbedding,normalizedBlocks,orderedZUnitary_matrix]

theorem normalizedBlocks_sub (A B : β → Matrix α γ ℂ) :
    normalizedBlocks A-normalizedBlocks B=normalizedBlocks (fun b => A b-B b) := by
  ext ⟨b,a⟩ j
  simp only [normalizedBlocks,Matrix.sub_apply,mul_sub]

/-- The first intertwining error in Step 3 is exactly the averaged error
in the statement of the count theorem. -/
theorem countEmbedding_shift_error {M d : Nat} (Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) (i : Fin M) :
    hsNorm ((cubeShift i*countEmbedding Z hZ-countEmbedding Z hZ*Z i)*s.xi)^2=aSquared Z s i := by
  have he : (cubeShift i*countEmbedding Z hZ-countEmbedding Z hZ*Z i)*s.xi=
      normalizedBlocks (fun g => (orderedZ Z (flip g i)-orderedZ Z g*Z i)*s.xi) := by
    rw [cubeShift_embedding,countEmbedding_right,normalizedBlocks_sub,normalizedBlocks_mul]
  rw [he,normalizedBlocks_hs_sq]
  simp only [aSquared,hs_eq_hsNorm,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

/-- The second intertwining error in Step 3 is exactly the signed average
in the statement. This is for the actual block operator X_i ⊗ F_i. -/
theorem countEmbedding_twist_error {M d : Nat} (X Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) (i : Fin M) :
    hsNorm ((cubeTwist (X i) i*countEmbedding Z hZ-countEmbedding Z hZ*X i)*s.xi)^2=bSquared X Z s i := by
  have he : (cubeTwist (X i) i*countEmbedding Z hZ-countEmbedding Z hZ*X i)*s.xi=
      normalizedBlocks (fun g => (bitSign g i • (X i*orderedZ Z g)-orderedZ Z g*X i)*s.xi) := by
    have hw : countEmbedding Z hZ=normalizedBlocks (fun g => orderedZ Z g) := by
      ext ⟨g,a⟩ b
      simp only [countEmbedding,uniformEmbedding,normalizedBlocks,orderedZUnitary_matrix]
    rw [hw,cubeTwist_normalizedBlocks,normalizedBlocks_mul,normalizedBlocks_sub,normalizedBlocks_mul]
  rw [he,normalizedBlocks_hs_sq]
  simp only [bSquared,bitSign,hs_eq_hsNorm,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

theorem countEmbedding_state_norm {M d : Nat} (Z : Fin M → Mat d)
    (hZ : ∀ i, IsInvolution (Z i)) (s : State d) : hsNorm (countEmbedding Z hZ*s.xi)=1 := by
  rw [countEmbedding_hs,hsNorm,hsSquared_trace,s.xi_positive.isHermitian.eq,s.xi_square,s.normalized]
  norm_num

end
end Companion.Analytic
