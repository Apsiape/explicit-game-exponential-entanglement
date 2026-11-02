import Companion.IndexedTwirl
import Mathlib.Tactic.Abel

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

theorem hs_smul {d : Nat} (c : ℂ) (A : Mat d) : hsNorm (c • A)=‖c‖*hsNorm A := by
  rw [hsNorm_eq_frobenius,norm_smul,hsNorm_eq_frobenius]

theorem hs_neg {d : Nat} (A : Mat d) : hsNorm (-A)=hsNorm A := by
  simp only [hsNorm_eq_frobenius,norm_neg]

theorem hs_sub_rev {d : Nat} (A B : Mat d) : hsNorm (A-B)=hsNorm (B-A) := by
  simp only [hsNorm_eq_frobenius,norm_sub_rev]

theorem hs_sub_le {d : Nat} (A B : Mat d) : hsNorm (A-B)≤hsNorm A+hsNorm B := by
  simpa only [hsNorm_eq_frobenius] using norm_sub_le A B

theorem signedCoefficient_norm {n : Nat} (sig g : Fin n → Bool) : ‖signedCoefficient sig g‖=1 := by
  induction n with
  | zero => simp [signedCoefficient]
  | succ n ih =>
    rw [signedCoefficient_succ,norm_mul,ih]
    cases g 0 <;> cases sig 0 <;> norm_num

theorem signedCoefficient_positive {n : Nat} (g : Fin n → Bool) :
    signedCoefficient (fun _ => false) g=1 := by simp [signedCoefficient]

theorem orderedZ_unitary {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (g : Fin n → Bool) : IsUnitary (orderedZ Z g) := by
  rw [← orderedZUnitary_matrix Z hZ g]
  exact (orderedZUnitary Z hZ g).property

theorem conjugate_unitary_left {d : Nat} (F Y : Mat d) (hF : IsUnitary F) (hY : IsUnitary Y) :
    (F.conjTranspose*Y*F).conjTranspose*(F.conjTranspose*Y*F)=1 := by
  calc
    _=F.conjTranspose*(Y.conjTranspose*((F*F.conjTranspose)*Y))*F := by
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
    _=1 := by rw [hF.2,Matrix.one_mul,hY.1,Matrix.mul_one,hF.1]

theorem weighted_twirl_pointwise {d : Nat} (F Y xi : Mat d) (c : ℂ)
    (hF : IsUnitary F) (hY : IsUnitary Y) (hc : ‖c‖=1) :
    hsNorm ((c • (F.conjTranspose*Y*F)-Y)*xi)≤
      hsNorm (c • (F.conjTranspose*(Y*xi)*F)-Y*xi)+hsNorm (F.conjTranspose*xi*F-xi) := by
  have hh : (F.conjTranspose*Y*F)*(F.conjTranspose*xi*F)=F.conjTranspose*(Y*xi)*F := by
    calc
      _=F.conjTranspose*(Y*((F*F.conjTranspose)*xi))*F := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hF.2,Matrix.one_mul]
  have he : (c • (F.conjTranspose*Y*F)-Y)*xi=
      (c • (F.conjTranspose*(Y*xi)*F)-Y*xi)+c • ((F.conjTranspose*Y*F)*(xi-F.conjTranspose*xi*F)) := by
    rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_sub,hh,smul_sub]
    abel
  rw [he]
  have ht := hsNorm_add_le (c • (F.conjTranspose*(Y*xi)*F)-Y*xi)
    (c • ((F.conjTranspose*Y*F)*(xi-F.conjTranspose*xi*F)))
  rw [hs_smul,hc,one_mul,hsNorm_unitary_left _ _ (conjugate_unitary_left F Y hF hY),
    hs_sub_rev xi (F.conjTranspose*xi*F)] at ht
  exact ht

theorem weighted_twirl_bound {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (sig : Fin n → Bool) (Y xi : Mat d) (hY : IsUnitary Y) :
    (∑ g : Fin n → Bool,
      hsNorm ((signedCoefficient sig g • ((orderedZ Z g).conjTranspose*Y*orderedZ Z g)-Y)*xi)^2)/(2:ℝ)^n≤
      2*(∑ i, hsNorm (if sig i then anti (Z i) (Y*xi) else comm (Z i) (Y*xi))^2)+
      2*(∑ i, hsNorm (comm (Z i) xi)^2) := by
  let a := fun g => hsNorm (signedCoefficient sig g • ((orderedZ Z g).conjTranspose*(Y*xi)*orderedZ Z g)-Y*xi)
  let b := fun g => hsNorm ((orderedZ Z g).conjTranspose*xi*orderedZ Z g-xi)
  have hp (g : Fin n → Bool) :
      hsNorm ((signedCoefficient sig g • ((orderedZ Z g).conjTranspose*Y*orderedZ Z g)-Y)*xi)^2≤2*(a g)^2+2*(b g)^2 := by
    have h := weighted_twirl_pointwise (orderedZ Z g) Y xi (signedCoefficient sig g)
      (orderedZ_unitary Z hZ g) hY (signedCoefficient_norm sig g)
    have hs := (sq_le_sq₀ (hsNorm_nonneg _) (add_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))).mpr h
    change _≤2*(a g)^2+2*(b g)^2
    change _≤(a g+b g)^2 at hs
    nlinarith [sq_nonneg (a g-b g)]
  have hsum := div_le_div_of_nonneg_right (Finset.sum_le_sum (s:=Finset.univ) (fun g _ => hp g))
    (show (0:ℝ)≤2^n by positivity)
  have ha := signed_twirl_bound Z hZ sig (Y*xi)
  have hb := signed_twirl_bound Z hZ (fun _ => false) xi
  simp only [signedCoefficient_positive,one_smul,Bool.false_eq_true,↓reduceIte] at hb
  have he : (∑ g, (2*(a g)^2+2*(b g)^2))/(2:ℝ)^n=
      2*((∑ g, (a g)^2)/(2:ℝ)^n)+2*((∑ g, (b g)^2)/(2:ℝ)^n) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    ring
  rw [he] at hsum
  change (∑ g, (a g)^2)/(2:ℝ)^n≤_ at ha
  change (∑ g, (b g)^2)/(2:ℝ)^n≤_ at hb
  linarith

theorem comm_vector_bound {d : Nat} (Y Z xi : Mat d) (hY : IsUnitary Y) :
    hsNorm (comm Z (Y*xi))≤hsNorm (comm Y Z*xi)+hsNorm (comm Z xi) := by
  have he : comm Z (Y*xi)= -(comm Y Z*xi)+Y*comm Z xi := by
    simp only [comm,Matrix.mul_sub,Matrix.sub_mul,neg_sub,Matrix.mul_assoc]
    abel
  rw [he]
  have h := hsNorm_add_le (-(comm Y Z*xi)) (Y*comm Z xi)
  rwa [hs_neg,hsNorm_unitary_left Y _ hY.1] at h

theorem anti_vector_bound {d : Nat} (Y Z xi : Mat d) (hY : IsUnitary Y) :
    hsNorm (anti Z (Y*xi))≤hsNorm (anti Y Z*xi)+hsNorm (comm Z xi) := by
  have he : anti Z (Y*xi)=anti Y Z*xi-Y*comm Z xi := by
    simp only [anti,comm,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := hs_sub_le (anti Y Z*xi) (Y*comm Z xi)
  rwa [hsNorm_unitary_left Y _ hY.1] at h

theorem pairwise_twirl_bound {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (sig : Fin n → Bool) (Y xi : Mat d) (hY : IsUnitary Y) :
    (∑ g : Fin n → Bool,
      hsNorm ((signedCoefficient sig g • ((orderedZ Z g).conjTranspose*Y*orderedZ Z g)-Y)*xi)^2)/(2:ℝ)^n≤
      2*(∑ i, (hsNorm ((if sig i then anti Y (Z i) else comm Y (Z i))*xi)+hsNorm (comm (Z i) xi))^2)+
      2*(∑ i, hsNorm (comm (Z i) xi)^2) := by
  have h := weighted_twirl_bound Z hZ sig Y xi hY
  have he : (∑ i, hsNorm (if sig i then anti (Z i) (Y*xi) else comm (Z i) (Y*xi))^2)≤
      ∑ i, (hsNorm ((if sig i then anti Y (Z i) else comm Y (Z i))*xi)+hsNorm (comm (Z i) xi))^2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply (sq_le_sq₀ (hsNorm_nonneg _) (add_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))).mpr
    cases hs : sig i
    · simpa [hs] using comm_vector_bound Y (Z i) xi hY
    · simpa [hs] using anti_vector_bound Y (Z i) xi hY
  linarith

end
end Companion.Analytic.CountProof
