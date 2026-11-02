import Blueprint.A.WordAreaBounds
import Blueprint.A.PauliRelations

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic ASector PairProof Published AWordAreaProof
open scoped BigOperators ComplexOrder MatrixOrder

theorem inverse_letters (w : Word) (P : Nat → Prop) (hw : ∀ a∈w, P a.1) :
    ∀ a∈FreeGroup.invRev w, P a.1 := by
  intro a ha
  simp only [FreeGroup.invRev,List.mem_reverse,List.mem_map] at ha
  obtain ⟨b,hb,he⟩ := ha
  have hh := congrArg Prod.fst he
  change b.1=a.1 at hh
  rw [←hh]
  exact hw b hb

theorem comm_letters (v w : Word) (P : Nat → Prop)
    (hv : ∀ a∈v, P a.1) (hw : ∀ a∈w, P a.1) : ∀ a∈commWord v w, P a.1 := by
  intro a ha
  simp only [commWord,List.mem_append] at ha
  rcases ha with ((ha|ha)|ha)|ha
  · exact hv a ha
  · exact hw a ha
  · exact inverse_letters v P hv a ha
  · exact inverse_letters w P hw a ha

theorem word_comm_eval {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (v w : Word) :
    wordEval U (commWord v w)=wordEval U v*wordEval U w*
      (wordEval U v).conjTranspose*(wordEval U w).conjTranspose := by
  rw [←assignmentHom_word U hU,mk_word_comm]
  simp only [groupComm,map_mul,map_inv]
  change (assignmentHom U hU (FreeGroup.mk v):Mat d)*
    (assignmentHom U hU (FreeGroup.mk w):Mat d)*
    (assignmentHom U hU (FreeGroup.mk v):Mat d).conjTranspose*
    (assignmentHom U hU (FreeGroup.mk w):Mat d).conjTranspose=_
  rw [assignmentHom_word,assignmentHom_word]

theorem transport_eval {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (v : Word) (j : Nat) :
    wordEval U (transportLamp v j)=wordEval U v*U j*(wordEval U v).conjTranspose := by
  rw [←assignmentHom_word U hU,mk_transport,map_mul,map_mul,map_inv]
  change (assignmentHom U hU (FreeGroup.mk v):Mat d)*
    (assignmentHom U hU (FreeGroup.of j):Mat d)*
    (assignmentHom U hU (FreeGroup.mk v):Mat d).conjTranspose=_
  rw [assignmentHom_word]
  simp only [assignmentHom,FreeGroup.lift_apply_of,asUnitary]

theorem cross_bound_from_area (hlit : ConjugatorLengths) {d : Nat}
    (U : Nat → Mat d) (s : State d) (e : ℝ) (he : 0≤e) (hm : sourceModel U s e)
    (v w : Word) (hv : ∀ a∈v, 1≤a.1 ∧ a.1≤6) (hw : ∀ a∈w, 1≤a.1 ∧ a.1≤6)
    (ell L : Nat) (hell : 6≤ell) (hlv : v.length≤2*ell+1) (hlw : w.length≤2*ell+1)
    (hL : 100*ell≤L) (harea : FiniteArea.Area sourceRelator (FreeGroup.mk (commWord v w)) L)
    (X Z : Mat d) (hX : IsUnitary X) (hZ : IsUnitary Z)
    (hXA : hs ((X-wordEval U v)*s.xi)≤(2*ell+1)*e)
    (hZB : hs ((Z-wordEval U w)*s.xi)≤(2*ell+1)*e) :
    hs (comm X Z*s.xi)≤61*(L:ℝ)^2*e+26*ell*e := by
  have hlen : (commWord v w).length≤9*ell := by
    simp only [commWord,List.length_append,FreeGroup.invRev_length]
    omega
  have hword := source_area_estimate hlit U s e he hm (commWord v w)
    (comm_letters v w (fun j => 1≤j ∧ j≤6) hv hw) L harea
  have hcost : L*(1+2*((commWord v w).length+30*L))≤61*L^2 := by
    have hh : 1+2*((commWord v w).length+30*L)≤61*L := by omega
    have hh' := Nat.mul_le_mul_left L hh
    nlinarith only [hh']
  have hD : hs ((wordEval U v*wordEval U w*(wordEval U v).conjTranspose*
      (wordEval U w).conjTranspose-1)*s.xi)≤61*(L:ℝ)^2*e := by
    rw [←word_comm_eval U hm.1 v w]
    apply hword.trans
    apply mul_le_mul_of_nonneg_right _ he
    exact_mod_cast hcost
  have hA := wordEval_unitary U hm.1 v
  have hB := wordEval_unitary U hm.1 w
  have hcA : hs (comm (wordEval U v) s.xi)≤(2*ell+1)*e :=
    (source_word_comm U s e hm v hv).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hlv) he)
  have hcB : hs (comm (wordEval U w) s.xi)≤(2*ell+1)*e :=
    (source_word_comm U s e hm w hw).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hlw) he)
  have hc := commutator_from_group_defect _ _ s.xi hA hB
    (61*(L:ℝ)^2*e) ((2*ell+1)*e) hD hcA hcB
  have hh := commutator_replacement X Z _ _ s.xi hX hZ hA hB
    (61*(L:ℝ)^2*e+4*((2*ell+1)*e)) ((2*ell+1)*e) ((2*ell+1)*e) hc hXA hZB hcA hcB
  have hnum : (12:ℝ)*(2*ell+1)≤26*ell := by exact_mod_cast (by omega : 12*(2*ell+1)≤26*ell)
  have hmul := mul_le_mul_of_nonneg_right hnum he
  linarith

end
end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.inverse_letters
#print axioms Blueprint.ASectorProof.comm_letters
#print axioms Blueprint.ASectorProof.word_comm_eval
#print axioms Blueprint.ASectorProof.transport_eval
#print axioms Blueprint.ASectorProof.cross_bound_from_area
