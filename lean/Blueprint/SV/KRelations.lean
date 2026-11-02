import Blueprint.SV.BalancedInput
import Blueprint.RatesDefinitions

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic

theorem joined_conjugacy {G : Type*} [Group G] (F V S R T : G)
    (hF : F*F=1) (hV : V*V=1) (hS : V*S*V=R) (hR : F*R*F=T) :
    (F*V)*S*(F*V)⁻¹=T := by
  have hiF : F⁻¹=F := inv_eq_of_mul_eq_one_left hF
  have hiV : V⁻¹=V := inv_eq_of_mul_eq_one_left hV
  calc
    _ = F*(V*S*V)*F := by rw [mul_inv_rev,hiV,hiF]; group
    _ = T := by rw [hS,hR]

def kGroupAssignment {G : Type*} [Group G] (Q : Fin 13 → G) : Nat → G
  | 1 => Q 0
  | 2 => Q 1
  | 3 => Q 2
  | 4 => Q 8 * Q 9
  | 5 => Q 3 * Q 4
  | _ => 1

/-- The two generator removals recover every K relation and the centrality of c.
This implication is proved in arbitrary groups, independently of matrix models. -/
theorem balanced_K_relations {G : Type*} [Group G] (Q : Fin 13 → G)
    (hsq : ∀ j, Q j*Q j=1)
    (hc : ∀ i : Fin balancedInput.c0.length,
      let (a,b,c) := balancedInput.c0[i]; Q a*Q b*Q a=Q c)
    (hlin : Q 0*Q 1*Q 2=1) :
    (∀ r∈kRelators, FreeGroup.lift (kGroupAssignment Q) (FreeGroup.mk r)=1) ∧
      ∀ j : Nat, 1≤j → j≤5 → Commute (kGroupAssignment Q j) (kGroupAssignment Q 3) := by
  let a := Q 0
  let b := Q 1
  let c := Q 2
  let f := Q 3
  let v := Q 4
  let x := Q 8*Q 9
  let y := f*v
  have hYA : y*a*y⁻¹=b := joined_conjugacy (Q 3) (Q 4) (Q 0) (Q 5) (Q 1)
    (hsq 3) (hsq 4) (hc ⟨3,by decide⟩) (hc ⟨4,by decide⟩)
  have hYB : y*b*y⁻¹=a := joined_conjugacy (Q 3) (Q 4) (Q 1) (Q 6) (Q 0)
    (hsq 3) (hsq 4) (hc ⟨5,by decide⟩) (hc ⟨6,by decide⟩)
  have hXC : x*c*x⁻¹=c := joined_conjugacy (Q 8) (Q 9) (Q 2) (Q 10) (Q 2)
    (hsq 8) (hsq 9) (hc ⟨8,by decide⟩) (hc ⟨9,by decide⟩)
  have hXF : x*f*x⁻¹=f := joined_conjugacy (Q 8) (Q 9) (Q 3) (Q 11) (Q 3)
    (hsq 8) (hsq 9) (hc ⟨10,by decide⟩) (hc ⟨11,by decide⟩)
  have hXV : x*v*x⁻¹=Q 7 := joined_conjugacy (Q 8) (Q 9) (Q 4) (Q 12) (Q 7)
    (hsq 8) (hsq 9) (hc ⟨12,by decide⟩) (hc ⟨13,by decide⟩)
  have hW : v*f*v=Q 7 := hc ⟨7,by decide⟩
  have hXY : x*y*x⁻¹=y*y := by
    calc
      _ = (x*f*x⁻¹)*(x*v*x⁻¹) := by dsimp [y]; group
      _ = f*(v*f*v) := by rw [hXF,hXV,←hW]
      _ = y*y := by dsimp [y]; group
  have hAB : a*b=c := by
    have hh := congrArg (fun z => z*c) hlin
    simpa only [a,b,c,mul_assoc,hsq 2,mul_one,one_mul] using hh
  have hBA : b*a=c := by
    have hh := congrArg (fun z : G => z⁻¹) hAB
    have hi (j : Fin 13) : (Q j)⁻¹=Q j := inv_eq_of_mul_eq_one_left (hsq j)
    simpa only [a,b,c,mul_inv_rev,hi] using hh
  have hAC : Commute a c := by
    rw [←hAB]
    exact (Commute.refl a).mul_right (by change a*b=b*a; exact hAB.trans hBA.symm)
  have hBC : Commute b c := by
    rw [←hBA]
    exact (Commute.refl b).mul_right (by change b*a=a*b; exact hBA.trans hAB.symm)
  have hYC : y*c*y⁻¹=c := by
    calc
      _ = (y*a*y⁻¹)*(y*b*y⁻¹) := by rw [←hAB]; group
      _ = c := by rw [hYA,hYB,hBA]
  have conj_comm (s : G) (h : s*c*s⁻¹=c) : Commute s c := by
    change s*c=c*s
    have hh := congrArg (fun z => z*s) h
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  constructor
  · intro r hr
    simp only [kRelators,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [FreeGroup.lift_mk,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,kGroupAssignment,Bool.false_eq_true,↓reduceIte,mul_one]
    · change x*(y*(x⁻¹*(y⁻¹*y⁻¹)))=1
      rw [←mul_assoc,←mul_assoc,hXY]
      group
    · change x*(c*(x⁻¹*c⁻¹))=1
      rw [←mul_assoc,←mul_assoc,hXC]
      group
    · change y*(a*(y⁻¹*b⁻¹))=1
      rw [←mul_assoc,←mul_assoc,hYA]
      group
    · change y*(b*(y⁻¹*a⁻¹))=1
      rw [←mul_assoc,←mul_assoc,hYB]
      group
    · change c⁻¹*(a*b)=1
      rw [hAB,inv_mul_cancel]
    · exact hsq 0
    · exact hsq 1
    · exact hsq 2
  · intro j hj1 hj5
    interval_cases j
    · exact hAC
    · exact hBC
    · exact Commute.refl _
    · exact conj_comm x hXC
    · exact conj_comm y hYC

/-- K's relations and the commutator marker hold in every solution of the
constructed presentation; no injectivity or embedding theorem is assumed. -/
theorem solution_K_data {G : Type} [Group G]
    (X : GeneralGadget.Variable balancedInput → G) (J : G)
    (h : GeneralGadget.Solution X J) :
    let Q := fun j : Fin 13 => X (GeneralGadget.old (GeneralGadget.nOld (GeneralGadget.hOld j)))
    let U := kGroupAssignment Q
    (∀ r∈kRelators, FreeGroup.lift U (FreeGroup.mk r)=1) ∧
      (∀ j : Nat, 1≤j → j≤5 → Commute (U j) (U 3)) ∧
      ∃ z : G, U 3*z*(U 3)⁻¹*z⁻¹=J := by
  let Q := fun j : Fin 13 => X (GeneralGadget.old (GeneralGadget.nOld (GeneralGadget.hOld j)))
  have hsq (j : Fin 13) : Q j*Q j=1 := h.square _
  have hc (i : Fin balancedInput.c0.length) :
      let (a,b,c) := balancedInput.c0[i]; Q a*Q b*Q a=Q c :=
    h.host_conjugacy (.inl i)
  have hlin : Q 0*Q 1*Q 2=1 := by
    have hh := h.base_product (.inl ⟨0,by decide⟩)
    change 1*(Q 0*(Q 1*(Q 2*1)))=1 at hh
    simpa only [one_mul,mul_one,mul_assoc] using hh
  obtain ⟨hrel,hcentral⟩ := balanced_K_relations Q hsq hc hlin
  refine ⟨hrel,hcentral,?_⟩
  let T := X (GeneralGadget.old (GeneralGadget.nOld (GeneralGadget.hT balancedInput)))
  refine ⟨T,?_⟩
  have hh := h.distinguished_relation
  simp only [GeneralGadget.distinguishedWord,GeneralGadget.evaluateFinal,map_mul,map_inv,
    FreeGroup.lift_apply_of,Option.elim_some,Option.elim_none] at hh
  change (Q 2)*T*(Q 2)⁻¹*T⁻¹*J=1 at hh
  change (Q 2)*T*(Q 2)⁻¹*T⁻¹=J
  have hJ : J⁻¹=J := inv_eq_of_mul_eq_one_left h.j_square
  exact (eq_inv_of_mul_eq_one_left hh).trans hJ

end
end Blueprint.SV

#print axioms Blueprint.SV.joined_conjugacy
#print axioms Blueprint.SV.kGroupAssignment
#print axioms Blueprint.SV.balanced_K_relations
#print axioms Blueprint.SV.solution_K_data
