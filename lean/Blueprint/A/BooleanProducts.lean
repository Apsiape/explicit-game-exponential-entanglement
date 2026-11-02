import Blueprint.A.AreaDistance

namespace Blueprint.PairProof
open Companion ASector
open scoped BigOperators

def cube {α : Type} : (n : Nat) → (Fin n → FreeGroup α) → (Fin n → Bool) → FreeGroup α
  | 0,_,_ => 1
  | n+1,t,u => (if u 0 then t 0 else 1)*cube n (Fin.tail t) (Fin.tail u)

theorem area_comm_product {α ι κ : Type} {R : ι → FreeGroup α}
    (xs : List κ) (t : κ → FreeGroup α) (z : FreeGroup α) (L : Nat)
    (h : ∀ i∈xs, FiniteArea.Area R (groupComm (t i) z) L) :
    FiniteArea.Area R (groupComm (xs.map t).prod z) (xs.length*L) := by
  induction xs with
  | nil => simpa [groupComm] using area_one R 0
  | cons i xs ih =>
    have hh := area_comm_mul (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))
    simpa only [List.map_cons,List.prod_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hh

theorem cube_comm {α ι : Type} {R : ι → FreeGroup α} (n : Nat)
    (t : Fin n → FreeGroup α) (u : Fin n → Bool) (z : FreeGroup α) (L : Nat)
    (h : ∀ i, FiniteArea.Area R (groupComm (t i) z) L) :
    FiniteArea.Area R (groupComm (cube n t u) z) (n*L) := by
  induction n with
  | zero => simpa [cube,groupComm] using area_one R 0
  | succ n ih =>
    have hh : FiniteArea.Area R (groupComm (if u 0 then t 0 else 1) z) L := by
      split
      · exact h 0
      · simpa [groupComm] using area_one R L
    have ht := ih (Fin.tail t) (Fin.tail u) (fun j => h j.succ)
    have hm := area_comm_mul hh ht
    simpa only [cube,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hm

theorem cube_zero {α : Type} (n : Nat) (t : Fin n → FreeGroup α) :
    cube n t (fun _ => false)=1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hz : Fin.tail (fun _ : Fin (n+1) => false)=(fun _ : Fin n => false) := by funext i; rfl
    rw [cube,hz]
    simpa only [Bool.false_eq_true,↓reduceIte,one_mul] using ih (Fin.tail t)

theorem cube_one_bit {α : Type} (n : Nat) (t : Fin n → FreeGroup α) (i : Fin n) :
    cube n t (fun j => decide (j=i))=t i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [cube,decide_true,↓reduceIte]
      have hz : Fin.tail (fun k : Fin (n+1) => decide (k=0))=fun _ => false := by
        funext j
        simp [Fin.tail,Fin.succ_ne_zero]
      rw [hz,cube_zero,mul_one]
    · have h0 : (0:Fin (n+1))≠j.succ := Ne.symm (Fin.succ_ne_zero j)
      simp only [cube,h0,decide_false,Bool.false_eq_true,↓reduceIte,one_mul]
      have he : Fin.tail (fun k : Fin (n+1) => decide (k=j.succ))=fun k => decide (k=j) := by
        funext k
        simp [Fin.tail]
      rw [he]
      exact ih (Fin.tail t) j

theorem cube_mul_close {α ι : Type} {R : ι → FreeGroup α} (n : Nat)
    (t : Fin n → FreeGroup α) (L : Nat)
    (hsq : ∀ i, FiniteArea.Area R (t i*t i) 1)
    (hc : ∀ i j, FiniteArea.Area R (groupComm (t i) (t j)) L)
    (u v : Fin n → Bool) :
    Close R (cube n t u*cube n t v) (cube n t (fun i => u i ^^ v i)) (n^2*L+n) := by
  induction n with
  | zero => simpa [cube] using close_refl R 1
  | succ n ih =>
    let A := if u 0 then t 0 else 1
    let B := if v 0 then t 0 else 1
    let U := cube n (Fin.tail t) (Fin.tail u)
    let V := cube n (Fin.tail t) (Fin.tail v)
    let T := cube n (Fin.tail t) (fun i => u i.succ ^^ v i.succ)
    have hswap : Close R (U*B) (B*U) (n*L) := by
      by_cases hv : v 0=true
      · have h := cube_comm n (Fin.tail t) (Fin.tail u) (t 0) L (fun i => hc i.succ 0)
        simpa only [Close,groupComm,mul_inv_rev,mul_assoc,B,hv,↓reduceIte,U] using h
      · have hB : B=1 := by simp [B,hv]
        rw [hB,mul_one,one_mul]
        exact close_weaken (close_refl R U) (Nat.zero_le _)
    have hAB : Close R (A*B) (if u 0 ^^ v 0 then t 0 else 1) 1 := by
      cases hu : u 0 <;> cases hv : v 0 <;> simp [A,B,hu,hv]
      all_goals first
        | exact close_weaken (close_refl R _) (by omega)
        | simpa only [Close,inv_one,mul_one] using hsq 0
    have ht : Close R (U*V) T (n^2*L+n) :=
      ih (Fin.tail t) (fun i => hsq i.succ) (fun i j => hc i.succ j.succ) (Fin.tail u) (Fin.tail v)
    have hfirst : Close R ((A*U)*(B*V)) ((A*B)*(U*V)) (n*L) := by
      have h := close_right V (close_left A hswap)
      simpa only [mul_assoc] using h
    have hlast := close_mul hAB ht
    have h := close_trans hfirst hlast
    have hx : Fin.tail (fun i : Fin (n+1) => u i ^^ v i)=(fun i : Fin n => u i.succ ^^ v i.succ) := by
      funext i
      rfl
    apply close_weaken (by simpa only [cube,A,B,U,V,T,hx] using h)
    nlinarith

theorem cube_inverse_close {α ι : Type} {R : ι → FreeGroup α} (n : Nat)
    (t : Fin n → FreeGroup α) (L : Nat)
    (hsq : ∀ i, FiniteArea.Area R (t i*t i) 1)
    (hc : ∀ i j, FiniteArea.Area R (groupComm (t i) (t j)) L)
    (u : Fin n → Bool) : Close R (cube n t u)⁻¹ (cube n t u) (n^2*L+n) := by
  have hh := cube_mul_close n t L hsq hc u u
  have hz : (fun i => u i ^^ u i)=(fun _ => false) := by funext i; simp
  rw [hz,cube_zero] at hh
  have hi := close_left (cube n t u)⁻¹ hh
  have hj : Close R (cube n t u) (cube n t u)⁻¹ (n^2*L+n) := by simpa [mul_assoc] using hi
  exact close_symm hj

end Blueprint.PairProof

#print axioms Blueprint.PairProof.cube
#print axioms Blueprint.PairProof.area_comm_product
#print axioms Blueprint.PairProof.cube_comm
#print axioms Blueprint.PairProof.cube_zero
#print axioms Blueprint.PairProof.cube_one_bit
#print axioms Blueprint.PairProof.cube_mul_close
#print axioms Blueprint.PairProof.cube_inverse_close
