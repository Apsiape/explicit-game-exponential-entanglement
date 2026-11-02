import Blueprint.RatesDefinitions
import Blueprint.AWordArea

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def kHalfWord : Word := [(1,false),(5,true),(1,true),(5,false),(3,false)]
def kRelation : RelKey → Option Word
  | .square j => kRelators[j]?
  | _ => none
def kHalfFactors : List Factor := [
  ⟨.square 2,true,[(1,false)]⟩,
  ⟨.square 5,false,[]⟩,
  ⟨.square 4,true,[(3,true)]⟩]

theorem kHalfFactors_valid : ∀ f∈kHalfFactors, (kRelation f.key).isSome=true := by decide
theorem kHalfWord_certificate :
    FreeGroup.mk (expandWith kRelation kHalfFactors)=FreeGroup.mk kHalfWord := by decide

theorem kHalfWord_defect {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j))
    (xi : Mat d) (e : ℝ)
    (hr : ∀ r∈kRelators, hs ((wordEval U r-1)*xi)≤e)
    (hc : ∀ j, hs (comm (U j) xi)≤e) :
    hs ((wordEval U kHalfWord-1)*xi)≤7*e := by
  have hrel : ∀ k r, kRelation k=some r → hs ((wordEval U r-1)*xi)≤e := by
    intro k r hk
    cases k <;> simp [kRelation] at hk
    rename_i j
    exact hr r (List.mem_iff_getElem?.mpr ⟨j,hk⟩)
  have h := AWordArea.charged_area kRelation U hU xi e e kHalfWord kHalfFactors
    kHalfFactors_valid kHalfWord_certificate hrel hc
  norm_num [kHalfFactors] at h
  linarith

theorem kHalfWord_identity {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) :
    wordEval U kHalfWord*(U 3*U 5)=(U 1).conjTranspose*U 5*U 1 := by
  simp only [kHalfWord,wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Bool.false_eq_true,↓reduceIte,Matrix.mul_one]
  calc
    _=(U 1).conjTranspose*U 5*U 1*(U 5).conjTranspose*((U 3).conjTranspose*U 3)*U 5 := by
      simp only [Matrix.mul_assoc]
    _=(U 1).conjTranspose*U 5*U 1*((U 5).conjTranspose*U 5) := by
      rw [(hU 3).1,Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _=_ := by rw [(hU 5).1,Matrix.mul_one]

def kAssignment {d : Nat} (U : Nat → Mat d) (j : Nat) : Mat d :=
  if 1≤j ∧ j≤5 then U j else 1

theorem kAssignment_relators {d : Nat} (U : Nat → Mat d) (r : Word) (hr : r∈kRelators) :
    wordEval (kAssignment U) r=wordEval U r := by
  simp only [kRelators,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> norm_num [wordEval,kAssignment]

theorem kFirstWord_identity {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) :
    wordEval U kRelators[0]*(U 5*U 5)=U 4*U 5*(U 4).conjTranspose := by
  simp only [kRelators,wordEval,List.getElem_cons_zero,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,Bool.false_eq_true,↓reduceIte,Matrix.mul_one]
  calc
    _=U 4*U 5*(U 4).conjTranspose*(U 5).conjTranspose*((U 5).conjTranspose*U 5)*U 5 := by
      simp only [Matrix.mul_assoc]
    _=U 4*U 5*(U 4).conjTranspose*((U 5).conjTranspose*U 5) := by
      rw [(hU 5).1,Matrix.mul_one]
      simp only [Matrix.mul_assoc,(hU 5).1,Matrix.mul_one]
    _=_ := by rw [(hU 5).1,Matrix.mul_one]

theorem hs_intertwiner_bound {d : Nat} (P Q xi : Mat d) :
    hs (P*xi-xi*Q)≤hs ((Q-P)*xi)+hs (comm Q xi) := by
  have he : P*xi-xi*Q= -((Q-P)*xi)+comm Q xi := by
    simp only [Companion.Analytic.comm,Matrix.sub_mul]
    abel
  rw [he,hs_eq_hsNorm]
  have h := hsNorm_add_le (-((Q-P)*xi)) (comm Q xi)
  rw [CountProof.hs_neg] at h
  exact h

end
end Blueprint.W2
