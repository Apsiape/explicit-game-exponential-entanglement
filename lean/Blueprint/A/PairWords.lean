import Blueprint.A.PairAreaBound

namespace Blueprint.PairProof
open Companion ASector

def cubeWord : (n : Nat) → (Fin n → Word) → (Fin n → Bool) → Word
  | 0,_,_ => []
  | n+1,t,u => (if u 0 then t 0 else [])++cubeWord n (Fin.tail t) (Fin.tail u)

theorem mk_cubeWord (n : Nat) (t : Fin n → Word) (u : Fin n → Bool) :
    FreeGroup.mk (cubeWord n t u)=cube n (fun i => FreeGroup.mk (t i)) u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : Fin.tail (fun i : Fin (n+1) => FreeGroup.mk (t i))=
        (fun i : Fin n => FreeGroup.mk (Fin.tail t i)) := by funext i; rfl
    simp only [cubeWord,←FreeGroup.mul_mk,cube,ht]
    rw [ih]
    cases hu : u 0 <;> simp [hu,←FreeGroup.one_eq_mk]

theorem cubeWord_length (n B : Nat) (t : Fin n → Word) (u : Fin n → Bool)
    (h : ∀ i, (t i).length≤B) : (cubeWord n t u).length≤n*B := by
  induction n with
  | zero => simp [cubeWord]
  | succ n ih =>
    have ht := ih (Fin.tail t) (Fin.tail u) (fun i => h i.succ)
    have hh : (if u 0 then t 0 else []).length≤B := by split; exact h 0; simp
    simp only [cubeWord,List.length_append,Nat.add_mul,Nat.one_mul]
    omega

theorem cubeWord_letters (n : Nat) (t : Fin n → Word) (u : Fin n → Bool)
    (P : Nat × Bool → Prop) (h : ∀ i a, a∈t i → P a) :
    ∀ a∈cubeWord n t u, P a := by
  induction n with
  | zero => simp [cubeWord]
  | succ n ih =>
    intro a ha
    simp only [cubeWord,List.mem_append] at ha
    rcases ha with ha | ha
    · split at ha
      · exact h 0 a ha
      · simp at ha
    · exact ih (Fin.tail t) (Fin.tail u) (fun i a ha => h i.succ a ha) a ha

theorem mk_transport (w : Word) (a : Nat) :
    FreeGroup.mk (transportLamp w a)=FreeGroup.mk w*FreeGroup.of a*(FreeGroup.mk w)⁻¹ := by
  simp only [transportLamp,←FreeGroup.mul_mk,FreeGroup.inv_mk]
  rfl

theorem mk_word_comm (v w : Word) :
    FreeGroup.mk (commWord v w)=groupComm (FreeGroup.mk v) (FreeGroup.mk w) := by
  simp only [commWord,groupComm,←FreeGroup.mul_mk,FreeGroup.inv_mk]

end Blueprint.PairProof

#print axioms Blueprint.PairProof.cubeWord
#print axioms Blueprint.PairProof.mk_cubeWord
#print axioms Blueprint.PairProof.cubeWord_length
#print axioms Blueprint.PairProof.cubeWord_letters
#print axioms Blueprint.PairProof.mk_transport
#print axioms Blueprint.PairProof.mk_word_comm
