import Blueprint.A.LampRounding
import Blueprint.SV.SectorVisibility

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem pair_product_difference {d : Nat} (X Z A B xi : Mat d)
    (hX : IsUnitary X) (hZ : IsUnitary Z) (hA : IsUnitary A) (hB : IsUnitary B)
    (F C : ℝ) (hXA : hs ((X-A)*xi)≤F) (hZB : hs ((Z-B)*xi)≤F)
    (hcB : hs (comm B xi)≤C) : hs ((X*Z-A*B)*xi)≤2*F+2*C := by
  have hm := ReturnProof.unitary_difference_right_transport X A B xi hX hA hB
  have ht := hsNorm_add_le (X*((Z-B)*xi)) ((X-A)*B*xi)
  rw [hsNorm_unitary_left _ _ hX.1] at ht
  have he : X*((Z-B)*xi)+(X-A)*B*xi=(X*Z-A*B)*xi := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he] at ht
  simp only [hs_eq_hsNorm] at *
  linarith

theorem commutator_from_group_defect {d : Nat} (A B xi : Mat d)
    (hA : IsUnitary A) (hB : IsUnitary B) (D C : ℝ)
    (hD : hs ((A*B*A.conjTranspose*B.conjTranspose-1)*xi)≤D)
    (hcA : hs (comm A xi)≤C) (hcB : hs (comm B xi)≤C) :
    hs (comm A B*xi)≤D+4*C := by
  let K := A*B*A.conjTranspose*B.conjTranspose
  have hK : IsUnitary K := ReturnProof.unitary_mul _ _
    (ReturnProof.unitary_mul _ _ (ReturnProof.unitary_mul _ _ hA hB) (ReturnProof.unitary_adjoint _ hA))
    (ReturnProof.unitary_adjoint _ hB)
  have hV := ReturnProof.unitary_mul B A hB hA
  have hc := ReturnProof.unitary_product_commutator B A xi hB hA
  have hh := ReturnProof.unitary_difference_right_transport K 1 (B*A) xi hK (by simp [IsUnitary]) hV
  have hcancel : K*(B*A)=A*B := by
    calc
      _=A*B*A.conjTranspose*(B.conjTranspose*B)*A := by simp only [K,Matrix.mul_assoc]
      _=A*B := by simp only [hB.1,Matrix.mul_one,Matrix.mul_assoc,hA.1,Matrix.mul_one]
  have he : (K-1)*(B*A)=comm A B := by
    rw [Matrix.sub_mul,hcancel,Matrix.one_mul]
    rfl
  rw [he] at hh
  change hs ((K-1)*xi)≤D at hD
  simp only [hs_eq_hsNorm] at *
  linarith

theorem commutator_replacement {d : Nat} (X Z A B xi : Mat d)
    (hX : IsUnitary X) (hZ : IsUnitary Z) (hA : IsUnitary A) (hB : IsUnitary B)
    (E F C : ℝ) (hE : hs (comm A B*xi)≤E)
    (hXA : hs ((X-A)*xi)≤F) (hZB : hs ((Z-B)*xi)≤F)
    (hcA : hs (comm A xi)≤C) (hcB : hs (comm B xi)≤C) :
    hs (comm X Z*xi)≤E+4*F+4*C := by
  have h1 := pair_product_difference X Z A B xi hX hZ hA hB F C hXA hZB hcB
  have h2 := pair_product_difference Z X B A xi hZ hX hB hA F C hZB hXA hcA
  have ht := hsNorm_add_le ((X*Z-A*B)*xi) (comm A B*xi)
  have hs := CountProof.hs_sub_le ((X*Z-A*B)*xi+comm A B*xi) ((Z*X-B*A)*xi)
  have he : (X*Z-A*B)*xi+comm A B*xi-(Z*X-B*A)*xi=comm X Z*xi := by
    simp only [Analytic.comm,Matrix.sub_mul]
    abel
  rw [he] at hs
  simp only [hs_eq_hsNorm] at *
  linarith

theorem marker_commutator {d : Nat} (X K J xi : Mat d)
    (hX : IsInvolution X) (hK : IsUnitary K) (hJ : IsInvolution J)
    (hXK : X*K*X=K.conjTranspose) (G C CJ : ℝ)
    (hG : hs ((K-J)*xi)≤G) (hC : hs (comm X xi)≤C) (hCJ : hs (comm J xi)≤CJ) :
    hs (comm X J*xi)≤2*G+4*C+2*CJ := by
  have hXu := CountProof.involution_unitary X hX
  have hJu := CountProof.involution_unitary J hJ
  have hKu := ReturnProof.unitary_adjoint K hK
  have hdiff : hs ((J-K)*xi)≤G := by
    have he : (J-K)*xi= -((K-J)*xi) := by simp only [Matrix.sub_mul]; abel
    rw [he,hs_eq_hsNorm,CountProof.hs_neg]
    exact hG
  have hadj := ReturnProof.unitary_difference_right_transport J K J xi hJu hK hJu
  have heAdj : (K.conjTranspose-J)*xi=K.conjTranspose*((J-K)*J*xi) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc,hJ.2,hK.1,
      Matrix.one_mul,Matrix.mul_one]
    rw [←Matrix.mul_assoc K.conjTranspose K (J*xi),hK.1,Matrix.one_mul]
  have hbAdj : hs ((K.conjTranspose-J)*xi)≤G+2*CJ := by
    rw [heAdj,hs_eq_hsNorm,hsNorm_unitary_left _ _ hKu.1]
    simp only [hs_eq_hsNorm] at *
    linarith
  have hmove := ReturnProof.unitary_difference_right_transport J K X xi hJu hK hXu
  have hs := hsNorm_add_le (X*((J-K)*X*xi)) ((K.conjTranspose-J)*xi)
  rw [hsNorm_unitary_left _ _ hXu.1] at hs
  have he : X*((J-K)*X*xi)+(K.conjTranspose-J)*xi=(X*J*X-J)*xi := by
    rw [←hXK]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he] at hs
  have hconj := ReturnProof.unitary_mul _ _ (ReturnProof.unitary_mul _ _ hXu hJu) hXu
  have hlast := ReturnProof.unitary_difference_right_transport (X*J*X) J X xi hconj hJu hXu
  have heLast : (X*J*X-J)*X=comm X J := by
    simp only [Matrix.sub_mul,Matrix.mul_assoc,hX.2,Matrix.mul_one,Analytic.comm]
  rw [heLast] at hlast
  simp only [hs_eq_hsNorm] at *
  linarith

end
end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.pair_product_difference
#print axioms Blueprint.ASectorProof.commutator_from_group_defect
#print axioms Blueprint.ASectorProof.commutator_replacement
#print axioms Blueprint.ASectorProof.marker_commutator
