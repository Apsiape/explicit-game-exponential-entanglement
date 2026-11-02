import Companion.POVMCompression
import Companion.Consistency

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

theorem unitary_list_product {d : Nat} (L : List (Mat d)) (hL : ∀ U ∈ L, IsUnitary U) :
    IsUnitary L.prod := by
  induction L with
  | nil => simp [IsUnitary]
  | cons U L ih =>
    have hU := hL U (by simp)
    have ht := ih (fun V hV => hL V (by simp [hV]))
    rw [List.prod_cons]
    constructor
    · rw [Matrix.conjTranspose_mul]
      calc
        _=L.prod.conjTranspose*(U.conjTranspose*U)*L.prod := by simp only [Matrix.mul_assoc]
        _=1 := by rw [hU.1,Matrix.mul_one,ht.1]
    · rw [Matrix.conjTranspose_mul]
      calc
        _=U*(L.prod*L.prod.conjTranspose)*U.conjTranspose := by simp only [Matrix.mul_assoc]
        _=1 := by rw [ht.2,Matrix.mul_one,hU.2]

/-- The exact telescoping estimate behind transfer, in the coefficient
matrix convention: Alice's transposes multiply on the right. -/
theorem intertwining_word_bound {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (L : List (Mat dB × Mat dA))
    (hL : ∀ p ∈ L, IsUnitary p.1 ∧ IsUnitary p.2) :
    hsNorm ((L.map Prod.fst).prod*psi-psi*(L.map Prod.snd).prod)≤
      (L.map (fun p => hsNorm (p.1*psi-psi*p.2))).sum := by
  induction L with
  | nil => simp [hsNorm,hsSquared]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ht : ∀ q ∈ L, IsUnitary q.1 ∧ IsUnitary q.2 := fun q hq => hL q (by simp [hq])
    have hR : IsUnitary (L.map Prod.snd).prod :=
      unitary_list_product _ (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact (ht q hq).2)
    have he : ((p.1*(L.map Prod.fst).prod)*psi-psi*(p.2*(L.map Prod.snd).prod))=
        p.1*((L.map Prod.fst).prod*psi-psi*(L.map Prod.snd).prod)+
          (p.1*psi-psi*p.2)*(L.map Prod.snd).prod := by
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
      abel
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [he]
    have h := hsNorm_add_le
      (p.1*((L.map Prod.fst).prod*psi-psi*(L.map Prod.snd).prod))
      ((p.1*psi-psi*p.2)*(L.map Prod.snd).prod)
    rw [hsNorm_unitary_left _ _ hp.1.1,hsNorm_unitary_right _ _ hR.2] at h
    linarith [ih ht]

theorem intertwining_word_uniform {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (L : List (Mat dB × Mat dA)) (theta : ℝ)
    (hL : ∀ p ∈ L, IsUnitary p.1 ∧ IsUnitary p.2)
    (he : ∀ p ∈ L, hsNorm (p.1*psi-psi*p.2)≤theta) :
    hsNorm ((L.map Prod.fst).prod*psi-psi*(L.map Prod.snd).prod)≤(L.length:ℝ)*theta := by
  apply (intertwining_word_bound psi L hL).trans
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := he p (by simp)
    have ht := ih (fun q hq => hL q (by simp [hq])) (fun q hq => he q (by simp [hq]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

/-- The factor 4 in transfer's within-equation commutator relation. -/
theorem commutator_relation_bound {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (B C : Mat dB) (A D : Mat dA) (hB : IsUnitary B) (hC : IsUnitary C)
    (hA : IsInvolution A) (hD : IsInvolution D) (hc : Commute A D)
    (theta : ℝ) (heB : hsNorm (B*psi-psi*A)≤theta) (heC : hsNorm (C*psi-psi*D)≤theta) :
    hsNorm ((B*C*B*C-1)*psi)≤4*theta := by
  have huA := CountProof.involution_unitary A hA
  have huD := CountProof.involution_unitary D hD
  have hL : ∀ p ∈ [(B,A),(C,D),(B,A),(C,D)], IsUnitary p.1 ∧ IsUnitary p.2 := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp|hp|hp|hp <;> subst p
    · exact ⟨hB,huA⟩
    · exact ⟨hC,huD⟩
    · exact ⟨hB,huA⟩
    · exact ⟨hC,huD⟩
  have he : ∀ p ∈ [(B,A),(C,D),(B,A),(C,D)], hsNorm (p.1*psi-psi*p.2)≤theta := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp|hp|hp|hp <;> subst p
    · exact heB
    · exact heC
    · exact heB
    · exact heC
  have hAD : A*D*A*D=1 := by
    calc
      _=A*(D*A)*D := by simp only [Matrix.mul_assoc]
      _=A*(A*D)*D := by rw [hc.symm.eq]
      _=(A*A)*(D*D) := by simp only [Matrix.mul_assoc]
      _=1 := by rw [hA.2,hD.2,Matrix.one_mul]
  have h := intertwining_word_uniform psi [(B,A),(C,D),(B,A),(C,D)] theta hL he
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Matrix.mul_one,
    List.length_cons,List.length_nil,Nat.cast_ofNat] at h
  have hAprod : A*(D*(A*D))=1 := by simpa only [Matrix.mul_assoc] using hAD
  rw [hAprod,Matrix.mul_one] at h
  norm_num at h
  simpa only [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc] using h

end
end Companion.Analytic.TransferProof
