import Blueprint.SV.AreaEncoding
import Blueprint.SV.PullbackRelations

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators

theorem k_central_group {G : Type} [Group G] (Q : Nat → G)
    (hrel : ∀ r∈kRelators, FreeGroup.lift Q (FreeGroup.mk r)=1) :
    ∀ j, 1≤j → j≤5 → Commute (Q j) (Q 3) := by
  let a := Q 1
  let b := Q 2
  let c := Q 3
  let x := Q 4
  let y := Q 5
  have hA : a*a=1 := by simpa [a,FreeGroup.lift_mk] using hrel [(1,true),(1,true)] (by simp [kRelators])
  have hB : b*b=1 := by simpa [b,FreeGroup.lift_mk] using hrel [(2,true),(2,true)] (by simp [kRelators])
  have hC : c*c=1 := by simpa [c,FreeGroup.lift_mk] using hrel [(3,true),(3,true)] (by simp [kRelators])
  have hAB : a*b=c := by
    have h := hrel [(3,false),(1,true),(2,true)] (by simp [kRelators])
    change c⁻¹*(a*(b*1))=1 at h
    simpa only [mul_one] using (inv_mul_eq_one.mp h).symm
  have hBA : b*a=c := by
    have h := congrArg (fun z : G => z⁻¹) hAB
    simpa only [mul_inv_rev,inv_eq_of_mul_eq_one_left hA,
      inv_eq_of_mul_eq_one_left hB,inv_eq_of_mul_eq_one_left hC] using h
  have hAC : Commute a c := by
    rw [←hAB]
    exact (Commute.refl a).mul_right (by change a*b=b*a; exact hAB.trans hBA.symm)
  have hBC : Commute b c := by
    rw [←hBA]
    exact (Commute.refl b).mul_right (by change b*a=a*b; exact hBA.trans hAB.symm)
  have hYA : y*a*y⁻¹=b := by
    have h := hrel [(5,true),(1,true),(5,false),(2,false)] (by simp [kRelators])
    have hh : (y*a*y⁻¹)*b⁻¹=1 := by simpa [a,b,y,FreeGroup.lift_mk,mul_assoc] using h
    exact mul_inv_eq_one.mp hh
  have hYB : y*b*y⁻¹=a := by
    have h := hrel [(5,true),(2,true),(5,false),(1,false)] (by simp [kRelators])
    have hh : (y*b*y⁻¹)*a⁻¹=1 := by simpa [a,b,y,FreeGroup.lift_mk,mul_assoc] using h
    exact mul_inv_eq_one.mp hh
  have hXC : x*c*x⁻¹=c := by
    have h := hrel [(4,true),(3,true),(4,false),(3,false)] (by simp [kRelators])
    have hh : (x*c*x⁻¹)*c⁻¹=1 := by simpa [x,c,FreeGroup.lift_mk,mul_assoc] using h
    exact mul_inv_eq_one.mp hh
  have hYC : y*c*y⁻¹=c := by
    calc
      _ = (y*a*y⁻¹)*(y*b*y⁻¹) := by rw [←hAB]; group
      _ = c := by rw [hYA,hYB,hBA]
  have conj_comm (s : G) (h : s*c*s⁻¹=c) : Commute s c := by
    change s*c=c*s
    have hh := congrArg (fun z => z*s) h
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  intro j hj1 hj5
  interval_cases j
  · exact hAC
  · exact hBC
  · exact Commute.refl _
  · exact conj_comm x hXC
  · exact conj_comm y hYC

def kRelationFunction : RelKey → Option Word
  | .equation i => kRelators[i]?
  | _ => none

theorem k_central_areas : ∀ j, 1≤j → j≤5 →
    ∃ k, HasAreaWith kRelationFunction (ASector.commWord [(j,true)] [(3,true)]) k := by
  let H := relationMap kRelationFunction
  let Q := fun j => H (FreeGroup.of j)
  have heval : FreeGroup.lift Q=H := by
    apply FreeGroup.ext_hom
    intro j
    simp [Q]
  have hrel : ∀ r∈kRelators, FreeGroup.lift Q (FreeGroup.mk r)=1 := by
    intro r hr
    rw [heval]
    obtain ⟨i,hi⟩ := List.mem_iff_getElem.mp hr
    exact relation_trivial kRelationFunction (.equation i) r (by
      simp only [kRelationFunction,List.getElem?_eq_getElem hi.1,hi.2])
  intro j hj1 hj5
  apply area_of_quotient
  have hc := k_central_group Q hrel j hj1 hj5
  change H (FreeGroup.mk (ASector.commWord [(j,true)] [(3,true)]))=1
  simp only [ASector.commWord,←FreeGroup.mul_mk,FreeGroup.inv_mk,map_mul,map_inv]
  change Q j*Q 3*(Q j)⁻¹*(Q 3)⁻¹=1
  rw [hc.eq]
  group

theorem k_central_constant : ∃ K : ℝ, 1≤K ∧ ∀ (d : Nat) (U : Nat → Mat d) e,
    0≤e → normalizedRepresentation kRelators U e →
    ∀ j, 1≤j → j≤5 → normalizedHS (wordEval U (ASector.commWord [(j,true)] [(3,true)])-1)≤K*e := by
  have hx : ∀ j : Fin 5, ∃ k,
      HasAreaWith kRelationFunction (ASector.commWord [(j.val+1,true)] [(3,true)]) k :=
    fun j => k_central_areas _ (by omega) (by omega)
  choose ks hks using hx
  let K : ℝ := 1+∑ j : Fin 5, (ks j:ℝ)
  have hsum : 0≤∑ j : Fin 5, (ks j:ℝ) := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  refine ⟨K,by dsimp [K]; linarith,?_⟩
  intro d U e he hrep j hj1 hj5
  let i : Fin 5 := ⟨j-1,by omega⟩
  have hi : i.val+1=j := by dsimp [i]; omega
  have ha := hks i
  rw [hi] at ha
  have hbound := HasAreaWith.length_bound (unitaryHSLength d) ha (assignmentHom U hrep.1) e he (by
    intro k r hr
    cases k <;> simp only [kRelationFunction] at hr
    all_goals try contradiction
    next n =>
      have hm : r∈kRelators := List.mem_of_getElem? hr
      simpa only [unitaryHSLength,assignmentHom_word] using hrep.2 r hm)
  change normalizedHS (((assignmentHom U hrep.1 (FreeGroup.mk _)):Mat d)-1)≤ks i*e at hbound
  rw [assignmentHom_word] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ he
  have hs : (ks i:ℝ)≤∑ j : Fin 5, (ks j:ℝ) :=
    Finset.single_le_sum (fun (j : Fin 5) _ => Nat.cast_nonneg (ks j)) (Finset.mem_univ i)
  dsimp [K]
  linarith

end
end Blueprint.SV

#print axioms Blueprint.SV.k_central_group
#print axioms Blueprint.SV.kRelationFunction
#print axioms Blueprint.SV.k_central_areas
#print axioms Blueprint.SV.k_central_constant
