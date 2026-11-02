import Blueprint.A.AreaDistance

namespace Blueprint.PairProof
open Companion ASector

theorem source_area (i : Fin pauliRelators.length) : FiniteArea.Area sourceRelator (sourceRelator i) 1 := by
  refine ⟨[(1,i,true)],by simp,?_⟩
  simp [FiniteArea.factorValue]

theorem source_word_area (w : Word) (hw : w∈pauliRelators) :
    FiniteArea.Area sourceRelator (FreeGroup.mk w) 1 := by
  obtain ⟨i,hi⟩ := List.mem_iff_getElem.mp hw
  have h := source_area ⟨i,hi.1⟩
  simpa only [sourceRelator,hi.2] using h

theorem linear_letter_comm (j a : Nat) (hj : j∈[1,2,4]) (ha : a∈[5,6]) :
    FiniteArea.Area sourceRelator (groupComm (FreeGroup.of j) (FreeGroup.of a)) 1 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj ha
  rcases hj with rfl|rfl|rfl <;> rcases ha with rfl|rfl
  all_goals exact source_word_area _ (by decide)

theorem word_lamp_comm (U : Word) (hU : ∀ x∈U, x.1∈[1,2,4]) (a : Nat) (ha : a∈[5,6]) :
    FiniteArea.Area sourceRelator (groupComm (FreeGroup.mk U) (FreeGroup.of a)) U.length := by
  induction U with
  | nil => simpa [groupComm,←FreeGroup.one_eq_mk] using area_one sourceRelator 0
  | cons x U ih =>
    rcases x with ⟨j,b⟩
    have hhead : FiniteArea.Area sourceRelator (groupComm (FreeGroup.mk [(j,b)]) (FreeGroup.of a)) 1 := by
      have h := linear_letter_comm j a (hU (j,b) (by simp)) ha
      cases b
      · exact area_comm_inv h
      · exact h
    have ht := ih (fun y hy => hU y (by simp [hy]))
    have h := area_comm_mul hhead ht
    simpa only [List.length_cons,Nat.one_add,FreeGroup.mul_mk,List.singleton_append] using h

theorem translated_square (U : FreeGroup Nat) :
    FiniteArea.Area sourceRelator ((U*FreeGroup.of 3*U⁻¹)*(U*FreeGroup.of 3*U⁻¹)) 1 := by
  have hs := source_word_area [(3,true),(3,true)] (by decide)
  have h := area_conj U hs
  convert h using 1
  change (U*FreeGroup.of 3*U⁻¹)*(U*FreeGroup.of 3*U⁻¹)=U*(FreeGroup.of 3*FreeGroup.of 3)*U⁻¹
  group

theorem nearest_lamp_comm (a b : Nat) (ha : a∈[5,6]) (hb : b∈[5,6]) :
    FiniteArea.Area sourceRelator
      (groupComm (FreeGroup.of a) (FreeGroup.of 3*FreeGroup.of b*(FreeGroup.of 3)⁻¹)) 1 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  all_goals exact source_word_area _ (by decide)

theorem transported_neighbour (U : Word) (hU : ∀ x∈U, x.1∈[1,2,4])
    (a b : Nat) (ha : a∈[5,6]) (hb : b∈[5,6]) :
    FiniteArea.Area sourceRelator
      (groupComm (FreeGroup.of a)
        ((FreeGroup.mk U*FreeGroup.of 3*(FreeGroup.mk U)⁻¹)*FreeGroup.of b*
          (FreeGroup.mk U*FreeGroup.of 3*(FreeGroup.mk U)⁻¹)⁻¹)) (4*U.length+1) := by
  let G := FreeGroup.mk U
  let t := FreeGroup.of 3
  let A := FreeGroup.of a
  let B := FreeGroup.of b
  have hA : Close sourceRelator (G⁻¹*A*G) A U.length := by
    have h := area_comm_inv (word_lamp_comm U hU a ha)
    simpa [Close,groupComm,G,A] using h
  have hB : Close sourceRelator (G⁻¹*B*G) B U.length := by
    have h := area_comm_inv (word_lamp_comm U hU b hb)
    simpa [Close,groupComm,G,B] using h
  have hC := close_comm hA (close_conj t hB)
  have hNear : Close sourceRelator (groupComm A (t*B*t⁻¹)) 1 1 :=
    close_to_one.mpr (nearest_lamp_comm a b ha hb)
  have h := area_conj G (close_to_one.mp (close_trans hC hNear))
  convert h using 1
  · dsimp [G,A,B,t,groupComm]
    simp only [←FreeGroup.inv_mk]
    group
  · omega

end Blueprint.PairProof

#print axioms Blueprint.PairProof.source_area
#print axioms Blueprint.PairProof.source_word_area
#print axioms Blueprint.PairProof.linear_letter_comm
#print axioms Blueprint.PairProof.word_lamp_comm
#print axioms Blueprint.PairProof.translated_square
#print axioms Blueprint.PairProof.nearest_lamp_comm
#print axioms Blueprint.PairProof.transported_neighbour
