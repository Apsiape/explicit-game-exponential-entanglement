import Blueprint.SV.PullbackRelations
import Blueprint.SV.NegativeSector

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators

theorem area_model_pullback (g : LCS) (images : Nat → Word) (z : Word)
    (hrel : ∀ r∈kRelators, ∃ k, HasArea g.system (substituteWords images r) k)
    (hcent : ∀ j, 1≤j → j≤5 → ∃ k, HasArea g.system
      (substituteWords images (ASector.commWord [(j,true)] [(3,true)])) k)
    (hmarker : ∃ k, HasArea g.system (ASector.commWord (images 3) z++[neg g.system.n]) k) :
    ∃ C : ℝ, 1≤C ∧ ∀ (d : Nat) e (m : Model g d e), 0≤e →
      m.U (g.system.n+1)=-1 → ∃ V : Nat → Mat d,
      (∀ j, IsUnitary (V j)) ∧
      (∀ r∈kRelators, hs ((wordEval V r-1)*m.state.xi)≤C*e) ∧
      (∀ j, 1≤j → j≤5 → hs (comm (V j) m.state.xi)≤C*e) ∧
      (∀ j, 1≤j → j≤5 → hs (comm (V j) (V 3)*m.state.xi)≤5*(C*e)) ∧
      1-3/2*(C*e)≤hs ((V 3-1)*m.state.xi) := by
  let cw := fun j => substituteWords images (ASector.commWord [(j,true)] [(3,true)])
  let marker := ASector.commWord (images 3) z++[neg g.system.n]
  let ws := kRelators.map (substituteWords images)++(List.range 5).map (fun j => cw (j+1))++[marker]
  have hws : ∀ w∈ws, ∃ k, HasArea g.system w k := by
    intro w hw
    simp only [ws,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with (⟨r,hr,rfl⟩ | ⟨j,hj,rfl⟩) | rfl
    · exact hrel r hr
    · exact hcent (j+1) (by omega) (by have := List.mem_range.mp hj; omega)
    · exact hmarker
  obtain ⟨D,hD,hbound⟩ := area_family_bound g.system ws hws
  let L : ℝ := ∑ j : Fin 5, ((images (j.val+1)).length:ℝ)
  let C : ℝ := D+L+z.length
  have hL : 0≤L := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  have hz : (0:ℝ)≤z.length := Nat.cast_nonneg _
  have hDC : D≤C := by dsimp [C]; linarith
  have hzC : (z.length:ℝ)≤C := by dsimp [C]; linarith
  have hlen : ∀ j, 1≤j → j≤5 → ((images j).length:ℝ)≤C := by
    intro j hj1 hj5
    let i : Fin 5 := ⟨j-1,by omega⟩
    have hi : ((images (i.val+1)).length:ℝ)≤L := by
      dsimp [L]
      exact Finset.single_le_sum (fun (k : Fin 5) _ => Nat.cast_nonneg ((images (k.val+1)).length))
        (Finset.mem_univ i)
    have he : i.val+1=j := by dsimp [i]; omega
    rw [he] at hi
    dsimp [C]
    linarith
  refine ⟨C,hD.trans hDC,?_⟩
  intro d e m he hJ
  let U := restrictAssignment g.system.n m.U
  have hU : ∀ j, IsUnitary (U j) := restricted_unitary _ _ m.unitary
  have hc : ∀ j, hs (comm (U j) m.state.xi)≤e :=
    restricted_commutator _ _ _ e he m.state_commutators
  have hr : ∀ k r, relator g.system k=some r → hs ((wordEval U r-1)*m.state.xi)≤e := by
    intro k r hk
    rw [restricted_word _ _ r (relator_support g.system k r hk)]
    exact m.relators k r hk
  have hall := hbound d U m.state.xi e he hU hr hc
  have hwbound (w : Word) (hw : w∈ws) : hs ((wordEval U w-1)*m.state.xi)≤C*e :=
    (hall w hw).trans (mul_le_mul_of_nonneg_right hDC he)
  let V := fun j => wordEval U (images j)
  have hV : ∀ j, IsUnitary (V j) := fun j => wordEval_unitary U hU _
  have hcV : ∀ j, 1≤j → j≤5 → hs (comm (V j) m.state.xi)≤C*e := by
    intro j hj1 hj5
    exact (AWordArea.word_commutator U hU m.state.xi e hc (images j)).trans
      (mul_le_mul_of_nonneg_right (hlen j hj1 hj5) he)
  have hcZ : hs (comm (wordEval U z) m.state.xi)≤C*e :=
    (AWordArea.word_commutator U hU m.state.xi e hc z).trans
      (mul_le_mul_of_nonneg_right hzC he)
  refine ⟨V,hV,?_,hcV,?_,?_⟩
  · intro r hmem
    rw [show wordEval V r=wordEval U (substituteWords images r) from AWordArea.word_eval_substitution U hU images r]
    apply hwbound
    simp only [ws,List.mem_append,List.mem_map,List.mem_singleton]
    exact Or.inl (Or.inl ⟨r,hmem,rfl⟩)
  · intro j hj1 hj5
    have hcomm : hs ((V j*V 3*(V j).conjTranspose*(V 3).conjTranspose-1)*m.state.xi)≤C*e := by
      have h := hwbound (cw j) (by
        simp only [ws,List.mem_append,List.mem_map,List.mem_singleton]
        refine Or.inl (Or.inr ⟨j-1,List.mem_range.mpr (by omega),?_⟩)
        rw [Nat.sub_add_cancel hj1])
      rw [←AWordArea.word_eval_substitution U hU images] at h
      rw [eval_comm_word V hV] at h
      simpa [wordEval] using h
    have hb := commutator_from_relator (V j) (V 3) m.state.xi (hV j) (hV 3)
    have hj := hcV j hj1 hj5
    have h3 := hcV 3 (by decide) (by decide)
    linarith
  · have hmark : hs ((V 3*wordEval U z*(V 3).conjTranspose*(wordEval U z).conjTranspose+1)*m.state.xi)≤C*e := by
      have h := hwbound marker (by simp [ws])
      have hUJ : U (g.system.n+1)=-1 := by
        dsimp [U,restrictAssignment]
        rw [ite_eq_left (by omega),hJ]
      dsimp [marker] at h
      rw [TransferProof.wordEval_append,eval_comm_word U hU] at h
      simp only [wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,neg,
        Bool.false_eq_true,↓reduceIte,hUJ,Matrix.conjTranspose_neg,Matrix.conjTranspose_one,
        Matrix.mul_one,Matrix.mul_neg] at h
      have heq : (- (V 3*wordEval U z*(V 3).conjTranspose*(wordEval U z).conjTranspose)-1)*m.state.xi=
          -((V 3*wordEval U z*(V 3).conjTranspose*(wordEval U z).conjTranspose+1)*m.state.xi) := by
        simp only [Matrix.neg_mul,Matrix.sub_mul,Matrix.add_mul,Matrix.one_mul]
        abel
      change hs ((-(V 3*wordEval U z*(V 3).conjTranspose*(wordEval U z).conjTranspose)-1)*m.state.xi)≤C*e at h
      rw [heq,hs_eq_hsNorm,CountProof.hs_neg,←hs_eq_hsNorm] at h
      exact h
    exact marker_visibility m.state (V 3) (wordEval U z) (hV 3) (wordEval_unitary U hU z) (C*e) hmark hcZ

end
end Blueprint.SV

#print axioms Blueprint.SV.area_model_pullback
