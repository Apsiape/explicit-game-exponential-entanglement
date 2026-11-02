import Companion.RoundingCommutator

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem unitary_mul {d : Nat} (U V : Mat d) (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U*V) :=
  (asUnitary U hU*asUnitary V hV).property

theorem unitary_adjoint {d : Nat} (U : Mat d) (hU : IsUnitary U) : IsUnitary U.conjTranspose := by
  simpa only [IsUnitary,Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1

theorem unitary_difference_left_bound {d : Nat} (P Q A : Mat d) (hP : IsUnitary P) (hQ : IsUnitary Q) :
    hsNorm ((P-Q)*A)≤2*hsNorm A := by
  rw [Matrix.sub_mul]
  have h := CountProof.hs_sub_le (P*A) (Q*A)
  rw [hsNorm_unitary_left _ _ hP.1,hsNorm_unitary_left _ _ hQ.1] at h
  linarith

theorem unitary_product_commutator {d : Nat} (U V xi : Mat d) (hU : IsUnitary U) (hV : IsUnitary V) :
    hsNorm (comm (U*V) xi)≤hsNorm (comm U xi)+hsNorm (comm V xi) := by
  have he : comm (U*V) xi=U*comm V xi+comm U xi*V := by
    simp only [comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := hsNorm_add_le (U*comm V xi) (comm U xi*V)
  rw [hsNorm_unitary_left _ _ hU.1,hsNorm_unitary_right _ _ hV.2] at h
  linarith

theorem unitary_difference_right_transport {d : Nat} (P Q V xi : Mat d)
    (hP : IsUnitary P) (hQ : IsUnitary Q) (hV : IsUnitary V) :
    hsNorm ((P-Q)*V*xi)≤hsNorm ((P-Q)*xi)+2*hsNorm (comm V xi) := by
  have he : (P-Q)*V*xi=((P-Q)*xi)*V+(P-Q)*comm V xi := by
    simp only [comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := hsNorm_add_le (((P-Q)*xi)*V) ((P-Q)*comm V xi)
  rw [hsNorm_unitary_right _ _ hV.2] at h
  have hb := unitary_difference_left_bound P Q (comm V xi) hP hQ
  linarith

theorem rounded_pair_product_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (j k : Fin g.system.n) :
    hsNorm ((roundedGenerators m j*roundedGenerators m k-m.U (j.val+1)*m.U (k.val+1))*m.state.xi)≤4*e := by
  let B := roundedGenerators m
  let U := fun j : Fin g.system.n => m.U (j.val+1)
  let xi := m.state.xi
  have he : (B j*B k-U j*U k)*xi=B j*((B k-U k)*xi)+(B j-U j)*U k*xi := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  have hBj : IsUnitary (B j) := CountProof.involution_unitary _ (roundedGenerators_involution m j)
  have hj := (rounded_generators_estimates m j).1
  have hk := (rounded_generators_estimates m k).1
  have hc := m.state_commutators (k.val+1) (by omega) (by have hh:=k.isLt; omega)
  change hsNorm (comm (U k) xi)≤e at hc
  have ht := unitary_difference_right_transport (B j) (U j) (U k) xi hBj (m.unitary _) (m.unitary _)
  have h := hsNorm_add_le (B j*((B k-U k)*xi)) ((B j-U j)*U k*xi)
  rw [hsNorm_unitary_left _ _ hBj.1] at h
  change hsNorm ((B j*B k-U j*U k)*xi)≤4*e
  rw [he]
  change hsNorm ((B j-U j)*xi)≤e at hj
  change hsNorm ((B k-U k)*xi)≤e at hk
  linarith

theorem model_commutator_relator_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j k : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars) (hk : k.val ∈ (g.system.equations[i.val]).vars) :
    hsNorm ((m.U (j.val+1)*m.U (k.val+1)*(m.U (j.val+1)).conjTranspose*(m.U (k.val+1)).conjTranspose-1)*m.state.xi)≤e := by
  have h := m.relators (.commute i.val j.val k.val) [pos j.val,pos k.val,neg j.val,neg k.val] (by
    simp [relator,List.getElem?_eq_getElem i.isLt,j.isLt,k.isLt,hj,hk])
  simpa only [wordEval,pos,neg,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Bool.false_eq_true,↓reduceIte,Matrix.mul_one,Matrix.mul_assoc,hs_eq_hsNorm] using h

theorem unrounded_commutator_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j k : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars) (hk : k.val ∈ (g.system.equations[i.val]).vars) :
    hsNorm (comm (m.U (j.val+1)) (m.U (k.val+1))*m.state.xi)≤5*e := by
  let A := m.U (j.val+1)
  let B := m.U (k.val+1)
  let R := A*B*A.conjTranspose*B.conjTranspose
  have hA : IsUnitary A := m.unitary _
  have hB : IsUnitary B := m.unitary _
  have hR : IsUnitary R := unitary_mul _ _ (unitary_mul _ _ (unitary_mul _ _ hA hB)
    (unitary_adjoint A hA)) (unitary_adjoint B hB)
  have hprod : IsUnitary (B*A) := unitary_mul B A hB hA
  have hEq : (R-1)*(B*A)=comm A B := by
    have hh : R*(B*A)=A*B := by
      calc
        _=A*B*(A.conjTranspose*(B.conjTranspose*B)*A) := by simp only [R,Matrix.mul_assoc]
        _=A*B := by rw [hB.1,Matrix.mul_one,hA.1,Matrix.mul_one]
    rw [Matrix.sub_mul,Matrix.one_mul,hh]
    rfl
  have hrel := model_commutator_relator_bound m i j k hj hk
  change hsNorm ((R-1)*m.state.xi)≤e at hrel
  have hcA := m.state_commutators (j.val+1) (by omega) (by have hh:=j.isLt; omega)
  have hcB := m.state_commutators (k.val+1) (by omega) (by have hh:=k.isLt; omega)
  change hsNorm (comm A m.state.xi)≤e at hcA
  change hsNorm (comm B m.state.xi)≤e at hcB
  have hp := unitary_product_commutator B A m.state.xi hB hA
  have ht := unitary_difference_right_transport R 1 (B*A) m.state.xi hR (by simp [IsUnitary]) hprod
  change hsNorm (comm A B*m.state.xi)≤5*e
  rw [hEq] at ht
  linarith

/-- The exact constant 13 in return's rounded within-equation pair bound. -/
theorem rounded_commutator_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j k : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars) (hk : k.val ∈ (g.system.equations[i.val]).vars) :
    hsNorm (comm (roundedGenerators m j) (roundedGenerators m k)*m.state.xi)≤13*e := by
  let B := roundedGenerators m
  let U := fun j : Fin g.system.n => m.U (j.val+1)
  let xi := m.state.xi
  have h1 := rounded_pair_product_bound m j k
  have h2 := unrounded_commutator_bound m i j k hj hk
  have h3 := rounded_pair_product_bound m k j
  have he : comm (B j) (B k)*xi=((B j*B k-U j*U k)*xi+comm (U j) (U k)*xi)-
      (B k*B j-U k*U j)*xi := by
    simp only [comm,Matrix.sub_mul,Matrix.mul_sub]
    abel
  have ha := hsNorm_add_le ((B j*B k-U j*U k)*xi) (comm (U j) (U k)*xi)
  have hb := CountProof.hs_sub_le ((B j*B k-U j*U k)*xi+comm (U j) (U k)*xi) ((B k*B j-U k*U j)*xi)
  change hsNorm ((B j*B k-U j*U k)*xi)≤4*e at h1
  change hsNorm (comm (U j) (U k)*xi)≤5*e at h2
  change hsNorm ((B k*B j-U k*U j)*xi)≤4*e at h3
  change hsNorm (comm (B j) (B k)*xi)≤13*e
  rw [he]
  linarith

end
end Companion.Analytic.ReturnProof
