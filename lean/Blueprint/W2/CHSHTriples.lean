import Blueprint.RatesDefinitions
import Companion.RoundedPairBounds

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem phase_unitary {d : Nat} (U : Mat d) (hU : IsUnitary U) :
    IsUnitary (Complex.I • U) := by
  constructor <;>
    simp [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,Complex.star_def,hU.1,hU.2]

theorem phase_hs {d : Nat} (U : Mat d) : hs (Complex.I • U)=hs U := by
  simpa [hs_eq_hsNorm] using CountProof.hs_smul Complex.I U

theorem phase_product_commutator {d : Nat} (A B xi : Mat d)
    (hA : IsUnitary A) (hB : IsUnitary B) :
    hs (comm (Complex.I • (A*B)) xi)≤hs (comm A xi)+hs (comm B xi) := by
  have he : comm (Complex.I • (A*B)) xi=Complex.I • comm (A*B) xi := by
    simp [Companion.Analytic.comm,Matrix.smul_mul,Matrix.mul_smul,smul_sub]
  rw [he,phase_hs]
  exact ReturnProof.unitary_product_commutator A B xi hA hB

theorem phase_square_defect {d : Nat} (A B xi : Mat d)
    (hA : IsInvolution A) (hB : IsInvolution B) :
    hs (((Complex.I • (A*B))*(Complex.I • (A*B))-1)*xi)=
      hs (anti A B*xi) := by
  have he : (Complex.I • (A*B))*(Complex.I • (A*B))-1= -(A*B)*anti A B := by
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I,
      neg_one_smul,anti,Matrix.mul_add,Matrix.neg_mul,Matrix.mul_neg]
    have hh : A*B*(B*A)=1 := by
      calc
        _=A*(B*B)*A := by noncomm_ring
        _=1 := by rw [hB.2,Matrix.mul_one,hA.2]
    rw [hh]
    abel
  rw [he,Matrix.neg_mul,Matrix.neg_mul,hs_eq_hsNorm,CountProof.hs_neg,
    Matrix.mul_assoc,hsNorm_unitary_left _ _
      (ReturnProof.unitary_mul A B (CountProof.involution_unitary A hA)
        (CountProof.involution_unitary B hB)).1]
  rfl

theorem signed_pair_replacement {d : Nat} (P Q U V xi : Mat d) (c : ℂ)
    (hc : ‖c‖=1) (hP : IsUnitary P) (hQ : IsUnitary Q)
    (hU : IsUnitary U) (hV : IsUnitary V) :
    hs ((P*Q-c • (Q*P))*xi)≤hs ((U*V-c • (V*U))*xi)+
      2*hs ((P-U)*xi)+2*hs ((Q-V)*xi)+2*hs (comm U xi)+2*hs (comm V xi) := by
  have product (P Q U V : Mat d) (hP : IsUnitary P) (hU : IsUnitary U)
      (hV : IsUnitary V) :
      hs ((P*Q-U*V)*xi)≤hs ((Q-V)*xi)+hs ((P-U)*xi)+2*hs (comm V xi) := by
    have he : (P*Q-U*V)*xi=P*((Q-V)*xi)+(P-U)*V*xi := by noncomm_ring
    have ht := ReturnProof.unitary_difference_right_transport P U V xi hP hU hV
    have h := hsNorm_add_le (P*((Q-V)*xi)) ((P-U)*V*xi)
    rw [hsNorm_unitary_left _ _ hP.1] at h
    rw [he,hs_eq_hsNorm]
    change hsNorm ((P-U)*V*xi)≤hs ((P-U)*xi)+2*hs (comm V xi) at ht
    simp only [←hs_eq_hsNorm] at *
    linarith
  have h1 := product P Q U V hP hU hV
  have h2 := product Q P V U hQ hV hU
  have he : (P*Q-c • (Q*P))*xi=((U*V-c • (V*U))*xi+
      (P*Q-U*V)*xi)-c • ((Q*P-V*U)*xi) := by
    simp only [Matrix.sub_mul,Matrix.smul_mul,smul_sub]
    abel
  have ht1 := hsNorm_add_le ((U*V-c • (V*U))*xi) ((P*Q-U*V)*xi)
  have ht2 := CountProof.hs_sub_le (((U*V-c • (V*U))*xi)+(P*Q-U*V)*xi)
    (c • ((Q*P-V*U)*xi))
  rw [CountProof.hs_smul,hc,one_mul] at ht2
  rw [he,hs_eq_hsNorm]
  simp only [←hs_eq_hsNorm] at *
  linarith

theorem anti_left_bound {d : Nat} (A B F : Mat d) (hA : IsUnitary A) (hB : IsUnitary B) :
    hs (anti A B*F)≤2*hs F := by
  have he : anti A B*F=A*(B*F)+B*(A*F) := by noncomm_ring [anti]
  rw [he,hs_eq_hsNorm]
  have h := hsNorm_add_le (A*(B*F)) (B*(A*F))
  rw [hsNorm_unitary_left _ _ hA.1,hsNorm_unitary_left _ _ hB.1,
    hsNorm_unitary_left _ _ hB.1,hsNorm_unitary_left _ _ hA.1] at h
  simp only [←hs_eq_hsNorm] at *
  linarith

theorem anti_right_transport {d : Nat} (A B V xi : Mat d)
    (hA : IsUnitary A) (hB : IsUnitary B) (hV : IsUnitary V) :
    hs (anti A B*V*xi)≤hs (anti A B*xi)+2*hs (comm V xi) := by
  have he : anti A B*V*xi=(anti A B*xi)*V+anti A B*comm V xi := by
    noncomm_ring [Companion.Analytic.comm]
  have ht := anti_left_bound A B (comm V xi) hA hB
  have h := hsNorm_add_le ((anti A B*xi)*V) (anti A B*comm V xi)
  rw [hsNorm_unitary_right _ _ hV.2] at h
  rw [he,hs_eq_hsNorm]
  simp only [←hs_eq_hsNorm] at *
  linarith

theorem rounded_phase_pair {d : Nat} (A B xi : Mat d)
    (hA : IsInvolution A) (hB : IsInvolution B) (hxi : xi.IsHermitian) :
    hs ((roundUnitary (Complex.I • (A*B))-Complex.I • (A*B))*xi)≤hs (anti A B*xi) ∧
      hs (comm (roundUnitary (Complex.I • (A*B))) xi)≤
        hs (comm A xi)+hs (comm B xi)+2*hs (anti A B*xi) := by
  have huA := CountProof.involution_unitary A hA
  have huB := CountProof.involution_unitary B hB
  have hu := phase_unitary (A*B) (ReturnProof.unitary_mul A B huA huB)
  have hr := ReturnProof.rounding_weighted_bound _ hu xi
  have hc := ReturnProof.rounding_commutator_bound _ xi hu hxi
  have hp := phase_product_commutator A B xi huA huB
  simp only [←hs_eq_hsNorm] at *
  rw [phase_square_defect A B xi hA hB] at hr hc
  exact ⟨hr,by linarith⟩

theorem phase_triple_anti {d : Nat} (A B C xi : Mat d)
    (hA : IsInvolution A) (hB : IsInvolution B) (hC : IsInvolution C) :
    hs (anti (Complex.I • (A*B)) (Complex.I • (B*C))*xi)≤
      hs (anti A B*xi)+hs (anti B C*xi)+hs (anti A C*xi)+
        4*hs (comm B xi)+2*hs (comm C xi) := by
  have huA := CountProof.involution_unitary A hA
  have huB := CountProof.involution_unitary B hB
  have huC := CountProof.involution_unitary C hC
  have huCB := ReturnProof.unitary_mul C B huC huB
  have he : anti (Complex.I • (A*B)) (Complex.I • (B*C))*xi=
      -B*(anti A C*B*xi)+(anti A B*(C*B)*xi)-(A*B)*(anti B C*xi) := by
    simp only [anti,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      Complex.I_mul_I,neg_one_smul]
    noncomm_ring
  have h1 := anti_right_transport A C B xi huA huC huB
  have h2 := anti_right_transport A B (C*B) xi huA huB huCB
  have hc := ReturnProof.unitary_product_commutator C B xi huC huB
  have ht1 := hsNorm_add_le (-B*(anti A C*B*xi)) (anti A B*(C*B)*xi)
  have ht2 := CountProof.hs_sub_le
    (-B*(anti A C*B*xi)+(anti A B*(C*B)*xi)) ((A*B)*(anti B C*xi))
  rw [Matrix.neg_mul,CountProof.hs_neg,hsNorm_unitary_left _ _ huB.1] at ht1
  rw [hsNorm_unitary_left _ _ (ReturnProof.unitary_mul A B huA huB).1] at ht2
  rw [he]
  simp only [←hs_eq_hsNorm,Matrix.neg_mul] at *
  linarith

theorem phase_cross_commutator {d : Nat} (A B C D xi : Mat d)
    (hA : IsUnitary A) (hB : IsUnitary B) (hC : IsUnitary C) (hD : IsUnitary D) :
    hs (comm (Complex.I • (A*B)) (Complex.I • (C*D))*xi)≤
      hs (anti B C*xi)+hs (anti A C*xi)+hs (anti B D*xi)+hs (anti A D*xi)+
        4*hs (comm B xi)+4*hs (comm D xi) := by
  have he : comm (Complex.I • (A*B)) (Complex.I • (C*D))*xi=
      -(A*(anti B C*D*xi)-anti A C*(B*D)*xi+
        (C*A)*(anti B D*xi)-C*(anti A D*B*xi)) := by
    simp only [Companion.Analytic.comm,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,Complex.I_mul_I,neg_one_smul]
    noncomm_ring [anti]
  have h1 := anti_right_transport B C D xi hB hC hD
  have h2 := anti_right_transport A C (B*D) xi hA hC (ReturnProof.unitary_mul B D hB hD)
  have h4 := anti_right_transport A D B xi hA hD hB
  have hc := ReturnProof.unitary_product_commutator B D xi hB hD
  have ht1 := CountProof.hs_sub_le (A*(anti B C*D*xi)) (anti A C*(B*D)*xi)
  have ht2 := hsNorm_add_le (A*(anti B C*D*xi)-anti A C*(B*D)*xi) ((C*A)*(anti B D*xi))
  have ht3 := CountProof.hs_sub_le
    (A*(anti B C*D*xi)-anti A C*(B*D)*xi+(C*A)*(anti B D*xi)) (C*(anti A D*B*xi))
  rw [hsNorm_unitary_left _ _ hA.1] at ht1
  rw [hsNorm_unitary_left _ _ (ReturnProof.unitary_mul C A hC hA).1] at ht2
  rw [hsNorm_unitary_left _ _ hC.1] at ht3
  rw [he,hs_eq_hsNorm,CountProof.hs_neg]
  simp only [←hs_eq_hsNorm] at *
  linarith

end
end Blueprint.W2
