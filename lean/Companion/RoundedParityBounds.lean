import Companion.RoundedPairBounds

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem unitary_list_commutator_bound {d : Nat} (L : List (Mat d)) (xi : Mat d) (e : ℝ)
    (hU : ∀ U ∈ L, IsUnitary U) (hc : ∀ U ∈ L, hsNorm (comm U xi)≤e) :
    hsNorm (comm L.prod xi)≤(L.length:ℝ)*e := by
  induction L with
  | nil => simp [comm,hsNorm,hsSquared]
  | cons U L ih =>
    have ht := ih (fun V hV => hU V (by simp [hV])) (fun V hV => hc V (by simp [hV]))
    have hp := TransferProof.unitary_list_product L (fun V hV => hU V (by simp [hV]))
    have h := unitary_product_commutator U L.prod xi (hU U (by simp)) hp
    have hhead := hc U (by simp)
    simp only [List.prod_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- Replacing q unitary factors costs q^2 e in the state-weighted norm.
Each original factor has state commutator at most e. -/
theorem unitary_list_replacement {d : Nat} (L : List (Mat d × Mat d)) (xi : Mat d) (e : ℝ)
    (hU : ∀ p ∈ L, IsUnitary p.1 ∧ IsUnitary p.2)
    (he : ∀ p ∈ L, hsNorm ((p.1-p.2)*xi)≤e)
    (hc : ∀ p ∈ L, hsNorm (comm p.2 xi)≤e) :
    hsNorm (((L.map Prod.fst).prod-(L.map Prod.snd).prod)*xi)≤(L.length:ℝ)^2*e := by
  induction L with
  | nil => simp [hsNorm,hsSquared]
  | cons p L ih =>
    have htail : ∀ q ∈ L, IsUnitary q.1 ∧ IsUnitary q.2 := fun q hq => hU q (by simp [hq])
    have hp := hU p (by simp)
    have herr := he p (by simp)
    have ht := ih htail (fun q hq => he q (by simp [hq])) (fun q hq => hc q (by simp [hq]))
    have hprod : IsUnitary (L.map Prod.snd).prod := TransferProof.unitary_list_product _ (by
      intro U h
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
      exact (htail q hq).2)
    have hcomm : hsNorm (comm (L.map Prod.snd).prod xi)≤(L.length:ℝ)*e := by
      have h := unitary_list_commutator_bound (L.map Prod.snd) xi e
        (by intro U h; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h; exact (htail q hq).2)
        (by intro U h; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h; exact hc q (by simp [hq]))
      simpa only [List.length_map] using h
    have hmove := unitary_difference_right_transport p.1 p.2 (L.map Prod.snd).prod xi hp.1 hp.2 hprod
    have hsum := hsNorm_add_le (p.1*(((L.map Prod.fst).prod-(L.map Prod.snd).prod)*xi))
      ((p.1-p.2)*(L.map Prod.snd).prod*xi)
    rw [hsNorm_unitary_left _ _ hp.1.1] at hsum
    have heq : ((p.1*(L.map Prod.fst).prod-p.2*(L.map Prod.snd).prod)*xi)=
        p.1*(((L.map Prod.fst).prod-(L.map Prod.snd).prod)*xi)+(p.1-p.2)*(L.map Prod.snd).prod*xi := by
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
      abel
    simp only [List.map_cons,List.prod_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [heq]
    nlinarith

theorem model_equation_relator_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) :
    hsNorm (((if (g.system.equations[i.val]).rhs then m.U (g.system.n+1)*
        ((g.system.equations[i.val]).vars.map (fun j => m.U (j+1))).prod else
        ((g.system.equations[i.val]).vars.map (fun j => m.U (j+1))).prod)-1)*m.state.xi)≤e := by
  have hb : (g.system.equations[i.val]).vars.all (· < g.system.n)=true :=
    List.all_eq_true.mpr (fun j hj => decide_eq_true (TransferProof.row_variable_bound g i j hj))
  have h := m.relators (.equation i.val)
    ((if (g.system.equations[i.val]).rhs then [pos g.system.n] else [])++(g.system.equations[i.val]).vars.map pos)
    (by
      simp [relator,List.getElem?_eq_getElem i.isLt]
      exact fun j hj => TransferProof.row_variable_bound g i j hj)
  cases hh : (g.system.equations[i.val]).rhs <;>
    simpa only [hh,Bool.false_eq_true,↓reduceIte,wordEval,pos,List.map_append,List.prod_append,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,List.map_map,Function.comp_def,Matrix.mul_one,
      Matrix.one_mul,hs_eq_hsNorm] using h

theorem unrounded_parity_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (he : 0≤e)
    (i : Fin g.system.equations.length) :
    hsNorm ((((g.system.equations[i.val]).vars.map (fun j => m.U (j+1))).prod-
      TransferProof.boolPhase (g.system.equations[i.val]).rhs • (1:Mat d))*m.state.xi)≤2*e := by
  let U := ((g.system.equations[i.val]).vars.map (fun j => m.U (j+1))).prod
  let J := m.U (g.system.n+1)
  have hJ : IsUnitary J := m.unitary _
  have hr := model_equation_relator_bound m i
  cases hh : (g.system.equations[i.val]).rhs
  · simp only [hh,Bool.false_eq_true,↓reduceIte] at hr
    change hsNorm ((U-TransferProof.boolPhase false • (1:Mat d))*m.state.xi)≤2*e
    simp only [TransferProof.boolPhase,Bool.false_eq_true,↓reduceIte,one_smul]
    exact hr.trans (by linarith)
  · simp only [hh,↓reduceIte] at hr
    have hv := m.central_visible
    change hsNorm ((J+1)*m.state.xi)≤e at hv
    change hsNorm ((J*U-1)*m.state.xi)≤e at hr
    have heq : (U+1)*m.state.xi=J.conjTranspose*((J*U-1)*m.state.xi)+J.conjTranspose*((J+1)*m.state.xi) := by
      simp only [Matrix.mul_sub,Matrix.mul_add,Matrix.sub_mul,Matrix.add_mul,← Matrix.mul_assoc,
        hJ.1,Matrix.one_mul]
      abel
    have hn := hsNorm_add_le (J.conjTranspose*((J*U-1)*m.state.xi)) (J.conjTranspose*((J+1)*m.state.xi))
    rw [hsNorm_unitary_left _ _ (unitary_adjoint J hJ).1,hsNorm_unitary_left _ _ (unitary_adjoint J hJ).1] at hn
    change hsNorm ((U-TransferProof.boolPhase true • (1:Mat d))*m.state.xi)≤2*e
    simp only [TransferProof.boolPhase,↓reduceIte,neg_one_smul,sub_neg_eq_add]
    rw [heq]
    linarith

theorem rounded_row_replacement {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) :
    hsNorm ((((g.system.equations[i.val]).vars.map (TransferProof.naturalBob (roundedGenerators m))).prod-
      ((g.system.equations[i.val]).vars.map (fun j => m.U (j+1))).prod)*m.state.xi)≤
        ((g.system.equations[i.val]).vars.length:ℝ)^2*e := by
  let vars := (g.system.equations[i.val]).vars
  let L := vars.map (fun j => (TransferProof.naturalBob (roundedGenerators m) j,m.U (j+1)))
  have hU : ∀ p ∈ L, IsUnitary p.1 ∧ IsUnitary p.2 := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hbound := TransferProof.row_variable_bound g i j hj
    change IsUnitary (TransferProof.naturalBob (roundedGenerators m) j) ∧ IsUnitary (m.U (j+1))
    simp only [TransferProof.naturalBob,hbound,↓reduceDIte]
    exact ⟨CountProof.involution_unitary _ (roundedGenerators_involution m _),m.unitary _⟩
  have herr : ∀ p ∈ L, hsNorm ((p.1-p.2)*m.state.xi)≤e := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hbound := TransferProof.row_variable_bound g i j hj
    simpa only [TransferProof.naturalBob,hbound,↓reduceDIte] using
      (rounded_generators_estimates m (⟨j,hbound⟩:Fin g.system.n)).1
  have hc : ∀ p ∈ L, hsNorm (comm p.2 m.state.xi)≤e := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hbound := TransferProof.row_variable_bound g i j hj
    exact m.state_commutators (j+1) (by omega) (by omega)
  have h := unitary_list_replacement L m.state.xi e hU herr hc
  simpa only [L,List.map_map,Function.comp_def,List.length_map] using h

/-- The parity defect used by return, with precisely (q^2+2)e. -/
theorem rounded_parity_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e) (he : 0≤e)
    (i : Fin g.system.equations.length) :
    hsNorm ((((g.system.equations[i.val]).vars.map (TransferProof.naturalBob (roundedGenerators m))).prod-
      TransferProof.boolPhase (g.system.equations[i.val]).rhs • (1:Mat d))*m.state.xi)≤
        (((g.system.equations[i.val]).vars.length:ℝ)^2+2)*e := by
  let B := ((g.system.equations[i.val]).vars.map (TransferProof.naturalBob (roundedGenerators m))).prod
  let U := ((g.system.equations[i.val]).vars.map (fun j => m.U (j+1))).prod
  let c := TransferProof.boolPhase (g.system.equations[i.val]).rhs
  have h1 := rounded_row_replacement m i
  have h2 := unrounded_parity_bound m he i
  have heq : (B-c • 1)*m.state.xi=(B-U)*m.state.xi+(U-c • 1)*m.state.xi := by
    simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul]
    abel
  change hsNorm ((B-c • 1)*m.state.xi)≤_
  rw [heq]
  have h := hsNorm_add_le ((B-U)*m.state.xi) ((U-c • 1)*m.state.xi)
  change hsNorm ((B-U)*m.state.xi)≤_ at h1
  change hsNorm ((U-c • 1)*m.state.xi)≤_ at h2
  nlinarith

end
end Companion.Analytic.ReturnProof
