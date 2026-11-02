import Companion.CountOrderedProducts

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

theorem sum_single_piece {n : Nat} (i : Fin n) (a : ℝ) (f : Fin n → ℝ) :
    (∑ j, if j=i then a else f j)=a+∑ j ∈ Finset.univ.filter (fun j => j≠i), f j := by
  rw [Finset.sum_ite]
  simp [Finset.filter_eq']

/-- Theorem C(i), with precisely the pairwise errors in Challenge.Count. -/
theorem count_a_bound {M d : Nat} (Z : Fin M → Mat d) (s : State d)
    (hZ : ∀ i, IsInvolution (Z i)) (i : Fin M) :
    aSquared Z s i≤
      2*(∑ j ∈ Finset.univ.filter (fun j => i<j),
        (hs (comm (Z i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2)+
      2*(∑ j ∈ Finset.univ.filter (fun j => i<j), hs (comm (Z j) s.xi)^2) := by
  have ha : aSquared Z s i=
      (∑ g : Fin M → Bool, hsNorm (((orderedZ (maskedZ Z (fun j => i<j)) g).conjTranspose*Z i*
        orderedZ (maskedZ Z (fun j => i<j)) g-Z i)*s.xi)^2)/(2:ℝ)^M := by
    unfold aSquared
    apply congrArg (fun v : ℝ => v/(2:ℝ)^M)
    apply Finset.sum_congr rfl
    intro g hg
    rw [hs_eq_hsNorm,a_pointwise_norm Z hZ]
  have h := pairwise_twirl_bound (maskedZ Z (fun j => i<j))
    (maskedZ_involution Z hZ _) (fun _ => false) (Z i) s.xi (involution_unitary _ (hZ i))
  simp only [signedCoefficient_positive,one_smul,Bool.false_eq_true,↓reduceIte] at h
  rw [← ha] at h
  have h1 (j : Fin M) :
      (hsNorm (comm (Z i) (maskedZ Z (fun j => i<j) j)*s.xi)+hsNorm (comm (maskedZ Z (fun j => i<j) j) s.xi))^2=
      if i<j then (hs (comm (Z i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2 else 0 := by
    by_cases hj : i<j <;>
      simp [maskedZ,hj,comm,hs_eq_hsNorm,hsNorm_eq_frobenius]
  have h2 (j : Fin M) : hsNorm (comm (maskedZ Z (fun j => i<j) j) s.xi)^2=
      if i<j then hs (comm (Z j) s.xi)^2 else 0 := by
    by_cases hj : i<j <;>
      simp [maskedZ,hj,comm,hs_eq_hsNorm,hsNorm_eq_frobenius]
  simp_rw [h1,h2] at h
  simpa only [Finset.sum_filter] using h

/-- Theorem C(ii), with the distinguished anticommutator and all off-diagonal
commutators, in the original statement's unnormalized HS convention. -/
theorem count_b_bound {M d : Nat} (X Z : Fin M → Mat d) (s : State d)
    (hX : ∀ i, IsInvolution (X i)) (hZ : ∀ i, IsInvolution (Z i)) (i : Fin M) :
    bSquared X Z s i≤
      2*(hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi))^2+
      2*(∑ j ∈ Finset.univ.filter (fun j => j≠i),
        (hs (comm (X i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2)+
      2*(∑ j, hs (comm (Z j) s.xi)^2) := by
  have ha : bSquared X Z s i=
      (∑ g : Fin M → Bool, hsNorm ((((if g i then (-1:ℂ) else 1) •
        ((orderedZ Z g).conjTranspose*X i*orderedZ Z g))-X i)*s.xi)^2)/(2:ℝ)^M := by
    unfold bSquared
    apply congrArg (fun v : ℝ => v/(2:ℝ)^M)
    apply Finset.sum_congr rfl
    intro g hg
    rw [hs_eq_hsNorm,intertwining_norm (orderedZ Z g) (X i) s.xi _ (orderedZ_unitary Z hZ g)]
  have h := pairwise_twirl_bound Z hZ (fun j => decide (j=i)) (X i) s.xi (involution_unitary _ (hX i))
  simp only [signedCoefficient_single] at h
  rw [← ha] at h
  have hc (j : Fin M) :
      (hsNorm ((if decide (j=i) then anti (X i) (Z j) else comm (X i) (Z j))*s.xi)+hsNorm (comm (Z j) s.xi))^2=
      if j=i then (hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi))^2 else
        (hs (comm (X i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2 := by
    by_cases hj : j=i
    · subst j; simp [hs_eq_hsNorm]
    · simp [hj,hs_eq_hsNorm]
  simp_rw [hc] at h
  rw [sum_single_piece] at h
  simpa only [hs_eq_hsNorm,mul_add,add_assoc] using h

end
end Companion.Analytic.CountProof
