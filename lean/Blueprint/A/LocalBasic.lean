import Blueprint.A.PairPresentation

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

theorem decode_source_relator (i : Fin pauliRelators.length) :
    FreeGroup.map decode (sourceRelator i)=paperRelator i := by
  fin_cases i <;> decide +kernel

theorem source_area_to_paper {w : FreeGroup Nat} {k : Nat}
    (h : FiniteArea.Area sourceRelator w k) :
    FiniteArea.Area paperRelator (FreeGroup.map decode w) k :=
  area_map (FreeGroup.map decode) decode_source_relator h

/-- The one-cell square clause of Lemma 7.7(a), for the exact paper words. -/
theorem paper_tau_square (i : Nat) : FiniteArea.Area paperRelator (paperTau i*paperTau i) 1 := by
  have h : FiniteArea.Area sourceRelator
      (FreeGroup.mk (tauWord i)*FreeGroup.mk (tauWord i)) 1 := by
    simpa only [tauWord,mk_transport] using translated_square (FreeGroup.mk (singleWord i))
  simpa only [map_mul,paperTau] using source_area_to_paper h

/-- Lemma 7.7(c), with its original transporter-length bound; no Dehn input. -/
theorem paper_transvection_lamp (i j : Nat) (a : Fin 2) :
    FiniteArea.Area paperRelator (groupComm (paperX i j) (paperLamp a))
      (2*(doubleWord i j).length+1) := by
  let U := doubleWord i j
  have ha : a.val+5∈[5,6] := by
    have := a.isLt
    have hh : a.val=0 ∨ a.val=1 := by omega
    rcases hh with hh|hh <;> simp [hh]
  have hG := word_lamp_comm U (fun x hx => by
    have h := double_letters i j x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto) (a.val+5) ha
  have hd := linear_letter_comm 4 (a.val+5) (by simp) ha
  have h := area_comm_mul (area_comm_mul hG hd) (area_comm_inv hG)
  have he : U.length+1+U.length=2*U.length+1 := by omega
  rw [he] at h
  have hs : FiniteArea.Area sourceRelator
      (groupComm (FreeGroup.mk (transvectionWord i j)) (FreeGroup.of (a.val+5))) (2*U.length+1) := by
    simpa only [transvectionWord,mk_transport,U] using h
  have haDecode : decode (a.val+5)= (⟨a.val+4,by have := a.isLt; omega⟩:Letter) := by
    fin_cases a <;> rfl
  simpa only [groupComm,map_mul,map_inv,paperX,paperLamp,FreeGroup.map.of,haDecode] using
    source_area_to_paper hs

/-- Lemma 7.7(d), with its original bound; only the listed certificate relators are used. -/
theorem paper_translated_neighbour (i : Nat) (a b : Fin 2) :
    FiniteArea.Area paperRelator
      (groupComm (paperLamp a) (paperTau i*paperLamp b*(paperTau i)⁻¹))
      (4*(singleWord i).length+1) := by
  have hl (a : Fin 2) : a.val+5∈[5,6] := by
    fin_cases a <;> simp
  have h := transported_neighbour (singleWord i) (fun x hx => by
    have h := omega_letters 0 i x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto) (a.val+5) (b.val+5) (hl a) (hl b)
  have hs : FiniteArea.Area sourceRelator
      (groupComm (FreeGroup.of (a.val+5))
        (FreeGroup.mk (tauWord i)*FreeGroup.of (b.val+5)*(FreeGroup.mk (tauWord i))⁻¹))
      (4*(singleWord i).length+1) := by
    simpa only [tauWord,mk_transport] using h
  have haDecode (a : Fin 2) : decode (a.val+5)= (⟨a.val+4,by have := a.isLt; omega⟩:Letter) := by
    fin_cases a <;> rfl
  simpa only [groupComm,map_mul,map_inv,paperTau,paperLamp,FreeGroup.map.of,haDecode] using
    source_area_to_paper hs

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.decode_source_relator
#print axioms Blueprint.PairProof.source_area_to_paper
#print axioms Blueprint.PairProof.paper_tau_square
#print axioms Blueprint.PairProof.paper_transvection_lamp
#print axioms Blueprint.PairProof.paper_translated_neighbour
