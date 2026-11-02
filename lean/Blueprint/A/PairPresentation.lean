import Blueprint.A.PaperPairInputs
import Blueprint.A.LampLocal

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

theorem area_map {α β ι : Type} {R : ι → FreeGroup α} {S : ι → FreeGroup β}
    (H : FreeGroup α →* FreeGroup β) (hR : ∀ i, H (R i)=S i)
    {w : FreeGroup α} {k : Nat} (h : FiniteArea.Area R w k) :
    FiniteArea.Area S (H w) k := by
  obtain ⟨fs,hf,he⟩ := h
  let F : FiniteArea.Factor α ι → FiniteArea.Factor β ι := fun f => (H f.1,f.2)
  refine ⟨fs.map F,by simpa using hf,?_⟩
  have hv (f : FiniteArea.Factor α ι) : FiniteArea.factorValue S (F f)=H (FiniteArea.factorValue R f) := by
    rcases f with ⟨q,i,b⟩
    cases b <;> simp [FiniteArea.factorValue,F,hR]
  simp only [List.map_map,Function.comp_def,hv]
  simpa only [map_list_prod,List.map_map,Function.comp_def] using congrArg H he

theorem encode_decode_relator (i : Fin 27) :
    FreeGroup.map encode (paperRelator i)=sourceRelator i := by
  fin_cases i <;> decide +kernel

theorem map_decode_mk (w : Word) (h : ∀ a∈w, 1≤a.1 ∧ a.1≤6) :
    FreeGroup.map encode (FreeGroup.map decode (FreeGroup.mk w))=FreeGroup.mk w := by
  have hf : ∀ a∈w, encode (decode a.1)=a.1 := by
    intro a ha
    have hh := h a ha
    simp only [encode,decode]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [FreeGroup.map.comp,FreeGroup.map.mk]
  apply congrArg FreeGroup.mk
  have hh : w.map (fun a => (encode (decode a.1),a.2))=w.map id := by
    apply List.map_congr_left
    intro a ha
    exact Prod.ext (hf a ha) rfl
  exact hh.trans (List.map_id w)

theorem omega_length (i j n : Nat) (hi : i<n) (hj : j<n) : (omegaWord i j).length<10*n := by
  by_cases he : i=j
  · simp [omegaWord,he]
    omega
  · have hmin : min i j<max i j := by omega
    have hmax : max i j<n := max_lt hi hj
    simp only [omegaWord,he,↓reduceIte,List.length_append,List.length_replicate,
      List.length_flatten,List.map_replicate,List.sum_replicate]
    simp
    omega

theorem omega_letters (i j : Nat) : ∀ a∈omegaWord i j, a.1∈[1,2] := by
  intro a ha
  simp only [omegaWord] at ha
  split at ha
  · simp at ha
  · simp only [List.mem_append,List.mem_flatten,List.mem_replicate] at ha
    rcases ha with (((ha|ha)|ha)|ha)|ha
    · obtain ⟨_,rfl⟩ := ha
      simp
    · obtain ⟨w,⟨_,rfl⟩,hw⟩ := ha
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (rfl|rfl|rfl|rfl)|rfl <;> simp
    · obtain ⟨w,⟨_,rfl⟩,hw⟩ := ha
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (rfl|rfl|rfl|rfl)|rfl <;> simp
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> simp
    · obtain ⟨_,rfl⟩ := ha
      simp

theorem single_length (i n : Nat) (hi : i<n) : (singleWord i).length<10*n :=
  omega_length 0 i n (by omega) hi

theorem double_length (i j n : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) :
    (doubleWord i j).length<20*n := by
  have hw : Equiv.swap 0 j i<n := by
    by_cases h0 : i=0
    · subst i; simpa using hj
    by_cases hij : i=j
    · subst i; simp; omega
    · rw [Equiv.swap_apply_of_ne_of_ne h0 hij]; exact hi
  have h1 := omega_length 0 j n (by omega) hj
  have h2 := omega_length 1 (Equiv.swap 0 j i) n (by omega) hw
  simpa only [doubleWord,List.length_append] using (by omega :
    (omegaWord 0 j).length+(omegaWord 1 (Equiv.swap 0 j i)).length<20*n)

theorem tau_length (i n : Nat) (hi : i<n) : (tauWord i).length≤21*n := by
  have h := single_length i n hi
  simp only [tauWord,transportLamp,List.length_append,List.length_cons,List.length_nil,FreeGroup.invRev_length]
  omega

theorem transport_letters (w : Word) (j : Nat) (P : Nat → Prop)
    (hw : ∀ a∈w, P a.1) (hj : P j) : ∀ a∈transportLamp w j, P a.1 := by
  intro a ha
  simp only [transportLamp,List.mem_append] at ha
  rcases ha with (ha|ha)|ha
  · exact hw a ha
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact hj
  · simp only [FreeGroup.invRev,List.mem_map,List.mem_reverse] at ha
    obtain ⟨b,hb,he⟩ := ha
    have he' := congrArg Prod.fst he
    change b.1=a.1 at he'
    rw [←he']
    exact hw b hb

theorem tau_letters (i : Nat) : ∀ a∈tauWord i, a.1∈[1,2,3] := by
  apply transport_letters (singleWord i) 3 (fun j => j∈[1,2,3]) _ (by simp)
  intro a ha
  have hh := omega_letters 0 i a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at *
  tauto

theorem double_letters (i j : Nat) : ∀ a∈doubleWord i j, a.1∈[1,2] := by
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · exact omega_letters 0 j a ha
  · exact omega_letters 1 (Equiv.swap 0 j i) a ha

theorem transvection_letters (i j : Nat) : ∀ a∈transvectionWord i j, 1≤a.1 ∧ a.1≤6 := by
  apply transport_letters (doubleWord i j) 4 (fun k => 1≤k ∧ k≤6) _ (by omega)
  intro a ha
  have hh := double_letters i j a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  omega

theorem mapped_tau (i : Nat) : FreeGroup.map encode (paperTau i)=FreeGroup.mk (tauWord i) := by
  apply map_decode_mk
  intro a ha
  have hh := tau_letters i a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  omega

theorem mapped_X (i j : Nat) : FreeGroup.map encode (paperX i j)=FreeGroup.mk (transvectionWord i j) :=
  map_decode_mk _ (transvection_letters i j)

theorem mapped_lamp (a : Fin 2) : FreeGroup.map encode (paperLamp a)=FreeGroup.of (a.val+5) := rfl

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.area_map
#print axioms Blueprint.PairProof.encode_decode_relator
#print axioms Blueprint.PairProof.map_decode_mk
#print axioms Blueprint.PairProof.omega_length
#print axioms Blueprint.PairProof.omega_letters
#print axioms Blueprint.PairProof.single_length
#print axioms Blueprint.PairProof.double_length
#print axioms Blueprint.PairProof.tau_length
#print axioms Blueprint.PairProof.transport_letters
#print axioms Blueprint.PairProof.tau_letters
#print axioms Blueprint.PairProof.double_letters
#print axioms Blueprint.PairProof.transvection_letters
#print axioms Blueprint.PairProof.mapped_tau
#print axioms Blueprint.PairProof.mapped_X
#print axioms Blueprint.PairProof.mapped_lamp
