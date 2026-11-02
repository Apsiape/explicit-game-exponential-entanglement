import Blueprint.A.Transvection

namespace Blueprint.PairProof
open Companion ASector
open scoped BigOperators

def clear {α : Type} {n : Nat} (X : Fin n → FreeGroup α) (j : Fin n) :
    List (Fin n) → (Fin n → Bool) → (Fin n → Bool) × FreeGroup α
  | [],u => (u,1)
  | i::ls,u =>
    if i≠j ∧ u i=true then
      let r := clear X j ls (Function.update u i false)
      (r.1,r.2*X i)
    else clear X j ls u

theorem clear_bits {α : Type} {n : Nat} (X : Fin n → FreeGroup α) (j : Fin n)
    (ls : List (Fin n)) (u : Fin n → Bool) (k : Fin n) :
    (clear X j ls u).1 k=if k≠j ∧ k∈ls then false else u k := by
  induction ls generalizing u with
  | nil => simp [clear]
  | cons i ls ih =>
    simp only [clear]
    split
    next hi =>
      rw [ih]
      by_cases hki : k=i <;> by_cases hkj : k=j <;> by_cases hkm : k∈ls <;>
        simp_all [Function.update_apply]
    next hi =>
      rw [ih]
      by_cases hki : k=i <;> by_cases hkj : k=j <;> by_cases hkm : k∈ls <;>
        cases hu : u i <;> simp_all

theorem clear_comm {α ι : Type} {n : Nat} {R : ι → FreeGroup α}
    (X : Fin n → FreeGroup α) (j : Fin n) (z : FreeGroup α) (B : Nat)
    (hX : ∀ i, i≠j → FiniteArea.Area R (groupComm (X i) z) B)
    (ls : List (Fin n)) (u : Fin n → Bool) :
    FiniteArea.Area R (groupComm (clear X j ls u).2 z) (ls.length*B) := by
  induction ls generalizing u with
  | nil => simpa [clear,groupComm] using area_one R 0
  | cons i ls ih =>
    simp only [clear]
    split
    next hi =>
      have h := area_comm_mul (ih (Function.update u i false)) (hX i hi.1)
      simpa only [List.length_cons,Nat.add_mul,Nat.one_mul] using h
    next =>
      exact area_weaken (ih u) (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega)

theorem clear_close {α ι : Type} {n : Nat} {R : ι → FreeGroup α}
    (t X : Fin n → FreeGroup α) (j : Fin n) (L : Nat) (hL : 1≤L)
    (hsq : ∀ k, FiniteArea.Area R (t k*t k) 1)
    (hc : ∀ k l, FiniteArea.Area R (groupComm (t k) (t l)) L)
    (hX : ∀ i, i≠j → ∀ k, Close R (X i*t k*(X i)⁻¹) (Function.update t j (t j*t i) k) L)
    (ls : List (Fin n)) (u : Fin n → Bool) (hj : u j=true) :
    Close R ((clear X j ls u).2*cube n t u*((clear X j ls u).2)⁻¹)
      (cube n t (clear X j ls u).1) (ls.length*(5*n^2*L)) := by
  have hn : 1≤n := by have := j.isLt; omega
  induction ls generalizing u with
  | nil => simpa [clear] using close_refl R (cube n t u)
  | cons i ls ih =>
    simp only [clear]
    split
    next hi =>
      let v := Function.update u i false
      let r := clear X j ls v
      have hv : v j=true := by simp [v,Ne.symm hi.1,hj]
      have ht := ih v hv
      have hs := cube_transvection n hn t i j (X i) L hL hsq hc (hX i hi.1) u hi.2 hj
      have hh := close_trans (close_conj r.2 hs) ht
      have he : (r.2*X i)*cube n t u*(r.2*X i)⁻¹=
          r.2*(X i*cube n t u*(X i)⁻¹)*r.2⁻¹ := by group
      change Close R ((r.2*X i)*cube n t u*(r.2*X i)⁻¹) (cube n t r.1) _
      rw [he]
      convert hh using 1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm]
    next =>
      exact close_weaken (ih u hj) (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega)

theorem clear_all {α ι : Type} {n : Nat} {R : ι → FreeGroup α}
    (t X : Fin n → FreeGroup α) (j : Fin n) (L B : Nat) (hL : 1≤L)
    (hsq : ∀ k, FiniteArea.Area R (t k*t k) 1)
    (hc : ∀ k l, FiniteArea.Area R (groupComm (t k) (t l)) L)
    (hX : ∀ i, i≠j → ∀ k, Close R (X i*t k*(X i)⁻¹) (Function.update t j (t j*t i) k) L)
    (u : Fin n → Bool) (hj : u j=true) :
    ∃ G : FreeGroup α, Close R (G*cube n t u*G⁻¹) (t j) (5*n^3*L) ∧
      ∀ z, (∀ i, i≠j → FiniteArea.Area R (groupComm (X i) z) B) →
        FiniteArea.Area R (groupComm G z) (n*B) := by
  let ls := List.finRange n
  let G := (clear X j ls u).2
  have hv : (clear X j ls u).1=(fun k => decide (k=j)) := by
    funext k
    rw [clear_bits]
    by_cases hk : k=j <;> simp [ls,hk,hj]
  refine ⟨G,?_,?_⟩
  · have h := clear_close t X j L hL hsq hc hX ls u hj
    rw [hv,cube_one_bit] at h
    convert h using 1
    simp only [ls,List.length_finRange]
    ring
  · intro z hz
    have h := clear_comm X j z B hz ls u
    simpa only [ls,List.length_finRange,G] using h

end Blueprint.PairProof

#print axioms Blueprint.PairProof.clear
#print axioms Blueprint.PairProof.clear_bits
#print axioms Blueprint.PairProof.clear_comm
#print axioms Blueprint.PairProof.clear_close
#print axioms Blueprint.PairProof.clear_all
