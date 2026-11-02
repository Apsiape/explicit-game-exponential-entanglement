import Blueprint.W2.CHSHPair

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 600000

theorem rectangular_smul_hs {a b : Nat} (P : Matrix (Fin a) (Fin b) ℂ) (c : ℂ) :
    hs (c • P)=‖c‖*hs P := by simp only [hs_eq_hsNorm,hsNorm_eq_frobenius,norm_smul]

theorem rectangular_neg_hs {a b : Nat} (P : Matrix (Fin a) (Fin b) ℂ) : hs (-P)=hs P := by
  simp only [hs_eq_hsNorm,hsNorm_eq_frobenius,norm_neg]

theorem rectangular_four_hs {a b : Nat} (P Q R S : Matrix (Fin a) (Fin b) ℂ) :
    hs (P+Q+R+S)≤hs P+hs Q+hs R+hs S := by
  have h1 := hsNorm_add_le P Q
  have h2 := hsNorm_add_le (P+Q) R
  have h3 := hsNorm_add_le (P+Q+R) S
  simp only [←hs_eq_hsNorm] at *
  linarith

theorem chshPlus_left_bound {a b : Nat} (B B' : Mat b) (P : Matrix (Fin b) (Fin a) ℂ)
    (hB : IsInvolution B) (hB' : IsInvolution B') :
    hs (chshPlus B B'*P)≤Real.sqrt 2*hs P := by
  have h0 := hsNorm_add_le (B*P) (B'*P)
  rw [hsNorm_unitary_left _ _ (CountProof.involution_unitary _ hB).1,
    hsNorm_unitary_left _ _ (CountProof.involution_unitary _ hB').1] at h0
  have hc : 2*(1/Real.sqrt 2:ℝ)=Real.sqrt 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have he : chshPlus B B'*P=(((1/Real.sqrt 2:ℝ):ℂ)) • (B*P+B'*P) := by
    simp [chshPlus,Matrix.smul_mul,Matrix.add_mul]
  rw [he,rectangular_smul_hs]
  have hcoef : ‖(((1/Real.sqrt 2:ℝ):ℂ))‖=(1/Real.sqrt 2:ℝ) := by
    simp [Complex.norm_real,abs_of_nonneg (by positivity : (0:ℝ)≤1/Real.sqrt 2)]
  rw [hcoef]
  simp only [←hs_eq_hsNorm] at h0
  calc
    _≤(1/Real.sqrt 2)*(hs P+hs P) := mul_le_mul_of_nonneg_left h0 (by positivity)
    _=Real.sqrt 2*hs P := by nlinarith [congrArg (fun r : ℝ => r*hs P) hc]

theorem pair_anti_linear {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A A' : Mat a) (B B' : Mat b) (hA : IsInvolution A) (hA' : IsInvolution A')
    (hB : IsInvolution B) (hB' : IsInvolution B') :
    hs (psi*(anti A A').transpose)≤(1+Real.sqrt 2)*
      (hs (chshPlus B B'*psi-psi*A.transpose)+hs (chshPlus B (-B')*psi-psi*A'.transpose)) := by
  let T := chshPlus B B'
  let T' := chshPlus B (-B')
  let E := T*psi-psi*A.transpose
  let E' := T'*psi-psi*A'.transpose
  have hz : T*T'+T'*T=0 := by
    have hh : (B+B')*(B-B')+(B-B')*(B+B')=0 := by
      calc
        _=(B*B+B*B)-(B'*B'+B'*B') := by noncomm_ring
        _=0 := by rw [hB.2,hB'.2]; abel
    simp only [T,T',chshPlus,←sub_eq_add_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [←smul_add,hh,smul_zero]
  have he : psi*(anti A A').transpose=(-E*A'.transpose)+(-E'*A.transpose)+(-T*E')+(-T'*E) := by
    symm
    calc
      _=psi*(anti A A').transpose-(T*T'+T'*T)*psi := by
        dsimp [E,E']
        simp only [anti,Matrix.transpose_add,Matrix.transpose_mul,Matrix.mul_add,Matrix.add_mul,
          Matrix.sub_mul,Matrix.mul_sub,Matrix.neg_mul,Matrix.mul_assoc]
        abel
      _=_ := by rw [hz,Matrix.zero_mul,sub_zero]
  have ht := rectangular_four_hs (-E*A'.transpose) (-E'*A.transpose) (-T*E') (-T'*E)
  have hEA : hs (-E*A'.transpose)=hs E := by
    rw [Matrix.neg_mul,rectangular_neg_hs,hs_eq_hsNorm,hsNorm_unitary_right _ _
      (CountProof.involution_unitary _ (ReturnProof.transpose_involution _ hA')).2]
    rfl
  have hE'A : hs (-E'*A.transpose)=hs E' := by
    rw [Matrix.neg_mul,rectangular_neg_hs,hs_eq_hsNorm,hsNorm_unitary_right _ _
      (CountProof.involution_unitary _ (ReturnProof.transpose_involution _ hA)).2]
    rfl
  have hTE := chshPlus_left_bound B B' E' hB hB'
  have hT'E := chshPlus_left_bound B (-B') E hB (neg_involution B' hB')
  rw [hEA,hE'A] at ht
  simp only [Matrix.neg_mul,rectangular_neg_hs] at ht
  rw [he]
  simp only [Matrix.neg_mul]
  change hs (_+_+_+_)≤(1+Real.sqrt 2)*(hs E+hs E')
  linarith

theorem state_pair_consistency {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Mat a) (T : Mat b) (hA : A.IsHermitian) (hT : T.IsHermitian)
    (s : State a) (hrho : s.rho=(psi.conjTranspose*psi).transpose) :
    hs (comm A s.xi)^2≤2*hs (T*psi-psi*A.transpose)^2 := by
  have hg : s.xi*s.xi=psi.transpose*psi.transpose.conjTranspose := by
    rw [s.xi_square,hrho,Matrix.transpose_mul,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
  have hc := rectangular_consistency_squared psi.transpose s.xi s.xi_positive hg A T.transpose hA hT.transpose
  have he : A*psi.transpose-psi.transpose*T.transpose= -(T*psi-psi*A.transpose).transpose := by
    simp only [Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_transpose]
    abel
  rw [he,rectangular_neg_hs,hs_transpose] at hc
  exact hc

end
end Blueprint.W2
