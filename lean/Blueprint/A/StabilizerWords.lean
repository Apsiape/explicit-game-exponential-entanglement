import Blueprint.A.PointShift
import Blueprint.A.FiniteSwapWords

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

def stabilizerHom (k : Nat) : FreeGroup Nat →* FreeGroup Nat := FreeGroup.lift fun j =>
  if j=1 ∨ j=2 then FreeGroup.mk (stabilizerWord k j) else 1

def stabilizerLetter (k : Nat) (a : Nat × Bool) : Word :=
  if a.1=1 ∨ a.1=2 then
    if a.2 then stabilizerWord k a.1 else FreeGroup.invRev (stabilizerWord k a.1)
  else []

def stabilizerExpand (k : Nat) (w : Word) : Word := (w.map (stabilizerLetter k)).flatten

theorem stabilizer_mk (k : Nat) (w : Word) :
    FreeGroup.mk (stabilizerExpand k w)=stabilizerHom k (FreeGroup.mk w) := by
  induction w with
  | nil => simp [stabilizerExpand,←FreeGroup.one_eq_mk]
  | cons a w ih =>
    simp only [stabilizerExpand,List.map_cons,List.flatten_cons,←FreeGroup.mul_mk] at *
    rw [ih]
    change _=stabilizerHom k (FreeGroup.mk [a]*FreeGroup.mk w)
    rw [map_mul]
    congr 1
    rcases a with ⟨j,b⟩
    cases b <;> by_cases hj : j=1 ∨ j=2
    all_goals simp [stabilizerLetter,stabilizerHom,hj,FreeGroup.lift_mk,←FreeGroup.inv_mk,←FreeGroup.one_eq_mk]

theorem stabilizer_point (k : Nat) (hk : k=1 ∨ k=2) :
    pointHom.comp (stabilizerHom k)=(shiftHom k).comp pointHom := by
  apply FreeGroup.ext_hom
  intro j
  simp only [MonoidHom.comp_apply,stabilizerHom,FreeGroup.lift_apply_of]
  split
  · rename_i hj
    exact (shiftHom_generators k hk j hj).symm
  · rename_i hj
    have h : pointHom (FreeGroup.of j)=1 := by
      simp only [pointHom,FreeGroup.lift_apply_of,ite_eq_right (fun h => hj (Or.inl h)),ite_eq_right (fun h => hj (Or.inr h))]
    rw [h,map_one,map_one]

theorem stabilizer_length (k : Nat) (hk : k=1 ∨ k=2) (w : Word) :
    (stabilizerExpand k w).length≤11*w.length := by
  have hl (a : Nat × Bool) : (stabilizerLetter k a).length≤11 := by
    rcases hk with rfl|rfl <;>
      simp [stabilizerLetter,stabilizerWord] <;> split_ifs <;> simp
  induction w with
  | nil => simp [stabilizerExpand]
  | cons a w ih =>
    have hh := hl a
    simp only [stabilizerExpand,List.map_cons,List.flatten_cons,List.length_append] at *
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem stabilizer_letter_comm (k : Nat) (hk : k=1 ∨ k=2) (j : Nat) (hj : j=1 ∨ j=2) :
    FiniteArea.Area sourceRelator
      (groupComm (FreeGroup.mk (stabilizerWord k j)) (FreeGroup.of (if k=1 then 3 else 4))) 1 := by
  rcases hk with rfl|rfl <;> rcases hj with rfl|rfl
  all_goals
    first
    | (convert area_inv (source_area ⟨5,by decide⟩) using 1; decide +kernel)
    | (convert area_inv (source_area ⟨6,by decide⟩) using 1; decide +kernel)
    | (convert area_inv (source_area ⟨7,by decide⟩) using 1; decide +kernel)
    | (convert area_inv (source_area ⟨8,by decide⟩) using 1; decide +kernel)

theorem stabilizer_word_comm (k : Nat) (hk : k=1 ∨ k=2) (w : Word) :
    FiniteArea.Area sourceRelator
      (groupComm (stabilizerHom k (FreeGroup.mk w)) (FreeGroup.of (if k=1 then 3 else 4))) w.length := by
  induction w with
  | nil => simpa [←FreeGroup.one_eq_mk,groupComm] using area_one sourceRelator 0
  | cons a w ih =>
    have hh : FiniteArea.Area sourceRelator
        (groupComm (stabilizerHom k (FreeGroup.mk [a])) (FreeGroup.of (if k=1 then 3 else 4))) 1 := by
      rcases a with ⟨j,b⟩
      by_cases hj : j=1 ∨ j=2
      · have hc := stabilizer_letter_comm k hk j hj
        cases b
        · simpa [stabilizerHom,FreeGroup.lift_mk,hj] using area_comm_inv hc
        · simpa [stabilizerHom,FreeGroup.lift_mk,hj] using hc
      · cases b <;> simpa [stabilizerHom,FreeGroup.lift_mk,hj,groupComm] using area_one sourceRelator 1
    have h := area_comm_mul hh ih
    simpa only [←map_mul,FreeGroup.mul_mk,List.singleton_append,List.length_cons,Nat.add_comm] using h

theorem stabilizer_omega (k : Nat) (hk : k=1 ∨ k=2) (i j : Nat) (hi : k ≤ i) (hj : k ≤ j) :
    pointHom (stabilizerHom k (FreeGroup.mk (omegaWord (i-k) (j-k))))=
      Equiv.swap (Concrete.Ray.one,i) (Concrete.Ray.one,j) := by
  rw [←MonoidHom.comp_apply,stabilizer_point k hk,MonoidHom.comp_apply,omega_permutation,shiftHom_swap,
    Nat.sub_add_cancel hi,Nat.sub_add_cancel hj]

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.stabilizerHom
#print axioms Blueprint.PairProof.stabilizerLetter
#print axioms Blueprint.PairProof.stabilizerExpand
#print axioms Blueprint.PairProof.stabilizer_mk
#print axioms Blueprint.PairProof.stabilizer_point
#print axioms Blueprint.PairProof.stabilizer_length
#print axioms Blueprint.PairProof.stabilizer_letter_comm
#print axioms Blueprint.PairProof.stabilizer_word_comm
#print axioms Blueprint.PairProof.stabilizer_omega
