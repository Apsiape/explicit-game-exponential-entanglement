import Blueprint.AWordArea
import Blueprint.A.ConjugatorLengths
import Blueprint.A.AreaCalculus

namespace Blueprint.AWordAreaProof
noncomputable section
open Companion Companion.Analytic Published AWordArea ASector

theorem charge_bound (fs : List Factor) (B : Nat)
    (h : ∀ f∈fs, f.conjugator.length≤B) : factorCharge fs≤fs.length*(1+2*B) := by
  induction fs with
  | nil => simp [factorCharge]
  | cons f fs ih =>
    have ht := ih (fun g hg => h g (by simp [hg]))
    have hh := h f (by simp)
    simp only [factorCharge,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega

theorem word_area_estimate (hlit : ConjugatorLengths) {d : Nat}
    (rfn : RelKey → Option Word) (K k : Nat) (w : Word)
    (hr : ∀ a r, rfn a=some r → r.length≤K) (ha : HasAreaWith rfn w k)
    (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (xi : Mat d) (e : ℝ) (he : 0≤e)
    (hrel : ∀ a r, rfn a=some r → hs ((wordEval U r-1)*xi)≤e)
    (hc : ∀ j, hs (comm (U j) xi)≤e) :
    hs ((wordEval U w-1)*xi)≤(k*(1+2*(w.length+k*K)):Nat)*e := by
  obtain ⟨fs,hfs,hv,hw,hshort⟩ := short_conjugators_of_finite hlit rfn K k w hr ha
  have hh := charged_area rfn U hU xi e e w fs hv hw hrel hc
  rw [factor_charge_scale] at hh
  have hb := (charge_bound fs (w.length+k*K) hshort).trans
    (Nat.mul_le_mul_right (1+2*(w.length+k*K)) hfs)
  exact hh.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) he)

def sourceLookup : RelKey → Option Word
  | .equation i => pauliRelators[i]?
  | _ => none

theorem source_lookup_at (i : Fin pauliRelators.length) :
    sourceLookup (.equation i.val)=some pauliRelators[i.val] := by
  simp [sourceLookup,List.getElem?_eq_getElem,i.isLt]

theorem source_area_to_words (w : Word) (k : Nat)
    (ha : FiniteArea.Area sourceRelator (FreeGroup.mk w) k) : HasAreaWith sourceLookup w k := by
  obtain ⟨fs,hfs,hw⟩ := ha
  let F : FiniteArea.Factor Nat (Fin pauliRelators.length) → Factor :=
    fun f => ⟨.equation f.2.1.val,f.2.2,f.1.toWord⟩
  refine ⟨fs.map F,by simpa using hfs,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    simp only [F,source_lookup_at,Option.isSome_some]
  · rw [mk_expandWith,List.map_map]
    convert hw using 1
    congr 1
    apply List.map_congr_left
    intro f hf
    change FreeGroup.mk (factorWordWith sourceLookup (F f))=FiniteArea.factorValue sourceRelator f
    rcases f with ⟨q,i,b⟩
    cases b <;> simp only [F,factorWordWith,source_lookup_at,Option.getD_some,
      Bool.false_eq_true,↓reduceIte,←FreeGroup.mul_mk,←FreeGroup.inv_mk,
      FreeGroup.mk_toWord,FiniteArea.factorValue,sourceRelator]

theorem source_lookup_mem {key : RelKey} {r : Word} (h : sourceLookup key=some r) : r∈pauliRelators := by
  cases key <;> simp only [sourceLookup,reduceCtorEq] at h
  exact List.mem_of_getElem? h

theorem source_alphabet : ∀ r∈pauliRelators, ∀ a∈r, 1≤a.1 ∧ a.1≤6 := by
  have hh : pauliRelators.all (fun r => r.all (fun a => decide (1≤a.1 ∧ a.1≤6)))=true := by decide +kernel
  intro r hr a ha
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hh r hr) a ha)

theorem source_lengths : ∀ r∈pauliRelators, r.length≤30 := by
  have hh : pauliRelators.all (fun r => decide (r.length≤30))=true := by decide +kernel
  exact fun r hr => of_decide_eq_true (List.all_eq_true.mp hh r hr)

theorem word_eval_congr_on {d : Nat} (U V : Nat → Mat d) (w : Word)
    (h : ∀ a∈w, U a.1=V a.1) : wordEval U w=wordEval V w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [wordEval,List.map_cons,List.prod_cons] at *
    rw [h a (by simp),ht]

theorem source_area_estimate (hlit : ConjugatorLengths) {d : Nat}
    (U : Nat → Mat d) (s : State d) (e : ℝ) (he : 0≤e) (hm : sourceModel U s e)
    (w : Word) (hw : ∀ a∈w, 1≤a.1 ∧ a.1≤6) (k : Nat)
    (ha : FiniteArea.Area sourceRelator (FreeGroup.mk w) k) :
    hs ((wordEval U w-1)*s.xi)≤(k*(1+2*(w.length+30*k)):Nat)*e := by
  let V : Nat → Mat d := fun j => if 1≤j ∧ j≤6 then U j else 1
  have hv : ∀ r : Word, (∀ a∈r, 1≤a.1 ∧ a.1≤6) → wordEval V r=wordEval U r := by
    intro r hr
    apply word_eval_congr_on
    intro a ha'
    exact if_pos (hr a ha')
  have hV : ∀ j, IsUnitary (V j) := by
    intro j
    dsimp [V]
    split
    · exact hm.1 j
    · simp [IsUnitary]
  have hcomm : ∀ j, hs (comm (V j) s.xi)≤e := by
    intro j
    dsimp [V]
    split
    · rename_i hj
      exact hm.2.2 j hj.1 hj.2
    · simpa [Analytic.comm,hs_eq_hsNorm,hsNorm,hsSquared] using he
  have hh := word_area_estimate hlit sourceLookup 30 k w
    (fun key r hr => source_lengths r (source_lookup_mem hr))
    (source_area_to_words w k ha) V hV s.xi e he
    (fun key r hr => by rw [hv r (source_alphabet r (source_lookup_mem hr))]; exact hm.2.1 r (source_lookup_mem hr))
    hcomm
  rw [hv w hw] at hh
  simpa only [Nat.mul_comm k 30] using hh

end
end Blueprint.AWordAreaProof

#print axioms Blueprint.AWordAreaProof.charge_bound
#print axioms Blueprint.AWordAreaProof.word_area_estimate
#print axioms Blueprint.AWordAreaProof.sourceLookup
#print axioms Blueprint.AWordAreaProof.source_lookup_at
#print axioms Blueprint.AWordAreaProof.source_area_to_words
#print axioms Blueprint.AWordAreaProof.source_lookup_mem
#print axioms Blueprint.AWordAreaProof.source_alphabet
#print axioms Blueprint.AWordAreaProof.source_lengths
#print axioms Blueprint.AWordAreaProof.word_eval_congr_on
#print axioms Blueprint.AWordAreaProof.source_area_estimate
