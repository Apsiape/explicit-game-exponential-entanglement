import Blueprint.AWordArea
import Blueprint.A.PairPresentation

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic ASector PairProof
open scoped BigOperators ComplexOrder MatrixOrder

theorem source_word_comm {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (hm : sourceModel U s e) (w : Word) (hw : ∀ a∈w, 1≤a.1 ∧ a.1≤6) :
    hs (comm (wordEval U w) s.xi)≤w.length*e :=
  AWordArea.word_commutator_on U hm.1 s.xi e w
    (fun a ha => hm.2.2 a.1 (hw a ha).1 (hw a ha).2)

theorem transported_lamp_square {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (hm : sourceModel U s e) (w : Word) (hw : ∀ a∈w, 1≤a.1 ∧ a.1≤6)
    (j : Nat) (hj : j∈[5,6]) :
    hs ((wordEval U (transportLamp w j)*wordEval U (transportLamp w j)-1)*s.xi)≤
      (2*w.length+1)*e := by
  have hr : hs ((U j*U j-1)*s.xi)≤e := by
    have hh := hm.2.1 [(j,true),(j,true)] (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl <;> decide +kernel)
    simpa [wordEval] using hh
  let G := wordEval U w
  have hG : IsUnitary G := wordEval_unitary U hm.1 w
  have heval : wordEval U (transportLamp w j)=G*U j*G.conjTranspose := by
    rw [←assignmentHom_word U hm.1,mk_transport,map_mul,map_mul,map_inv]
    change (assignmentHom U hm.1 (FreeGroup.mk w):Mat d)*
      (assignmentHom U hm.1 (FreeGroup.of j):Mat d)*
      (assignmentHom U hm.1 (FreeGroup.mk w):Mat d).conjTranspose=_
    rw [assignmentHom_word]
    simp only [assignmentHom,FreeGroup.lift_apply_of,asUnitary,G]
  have he : (G*U j*G.conjTranspose)*(G*U j*G.conjTranspose)=G*(U j*U j)*G.conjTranspose := by
    calc
      _=G*U j*(G.conjTranspose*G)*U j*G.conjTranspose := by simp only [Matrix.mul_assoc]
      _=_ := by simp only [hG.1,Matrix.mul_one,Matrix.mul_assoc]
  have hc := AWordArea.conjugation (U j*U j) G s.xi
    (ReturnProof.unitary_mul _ _ (hm.1 j) (hm.1 j)) hG
  rw [heval,he]
  have hg := source_word_comm U s e hm w hw
  change hs (comm G s.xi)≤w.length*e at hg
  have hb := hc.trans (add_le_add hr (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2)))
  convert hb using 1 <;> push_cast <;> ring

theorem transported_lamp_rounding {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (he : 0≤e) (hm : sourceModel U s e) (w : Word)
    (hw : ∀ a∈w, 1≤a.1 ∧ a.1≤6) (j : Nat) (hj : j∈[5,6])
    (ell : Nat) (hell : w.length≤ell) (hl : 3≤ell) :
    let A := wordEval U (transportLamp w j)
    let R := roundUnitary A
    IsInvolution R ∧ hs ((R-A)*s.xi)≤(2*ell+1)*e ∧ hs (comm R s.xi)≤7*ell*e := by
  let A := wordEval U (transportLamp w j)
  have hA : IsUnitary A := wordEval_unitary U hm.1 _
  have hsq := transported_lamp_square U s e hm w hw j hj
  have hsq' : hs ((A*A-1)*s.xi)≤(2*ell+1)*e := by
    apply hsq.trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 2*w.length+1≤2*ell+1)) he
  have hword : ∀ a∈transportLamp w j, 1≤a.1 ∧ a.1≤6 := by
    apply transport_letters w j (fun k => 1≤k ∧ k≤6) hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    omega
  have hc := source_word_comm U s e hm (transportLamp w j) hword
  have hlen : (transportLamp w j).length=2*w.length+1 := by
    simp only [transportLamp,List.length_append,List.length_cons,List.length_nil,FreeGroup.invRev_length]
    omega
  rw [hlen] at hc
  have hc' : hs (comm A s.xi)≤(2*ell+1)*e := hc.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 2*w.length+1≤2*ell+1)) he)
  have hr := ReturnProof.rounding_weighted_bound A hA s.xi
  have hrc := ReturnProof.rounding_commutator_bound A s.xi hA s.xi_positive.isHermitian
  dsimp only
  refine ⟨ReturnProof.roundUnitary_involution A,hr.trans hsq',?_⟩
  have hle : 3*(2*(ell:ℝ)+1)≤7*ell := by exact_mod_cast (by omega : 3*(2*ell+1)≤7*ell)
  have hh := mul_le_mul_of_nonneg_right hle he
  simp only [hs_eq_hsNorm] at *
  push_cast at *
  linarith

end
end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.source_word_comm
#print axioms Blueprint.ASectorProof.transported_lamp_square
#print axioms Blueprint.ASectorProof.transported_lamp_rounding
