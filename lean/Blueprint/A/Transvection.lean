import Blueprint.A.BooleanProducts

namespace Blueprint.PairProof
open Companion ASector
open scoped BigOperators

theorem cube_pointwise_close {α ι : Type} {R : ι → FreeGroup α} (n : Nat)
    (a b : Fin n → FreeGroup α) (u : Fin n → Bool) (L : Nat)
    (h : ∀ i, Close R (a i) (b i) L) : Close R (cube n a u) (cube n b u) (n*L) := by
  induction n with
  | zero => simpa [cube] using close_refl R 1
  | succ n ih =>
    have hhead : Close R (if u 0 then a 0 else 1) (if u 0 then b 0 else 1) L := by
      split
      · exact h 0
      · exact close_weaken (close_refl R 1) (Nat.zero_le _)
    have hh := close_mul hhead (ih (Fin.tail a) (Fin.tail b) (Fin.tail u) (fun j => h j.succ))
    simpa only [cube,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hh

theorem cube_conjugation {α : Type} (n : Nat) (t : Fin n → FreeGroup α) (u : Fin n → Bool)
    (X : FreeGroup α) : X*cube n t u*X⁻¹=cube n (fun i => X*t i*X⁻¹) u := by
  induction n with
  | zero => simp [cube]
  | succ n ih =>
    have he : Fin.tail (fun i : Fin (n+1) => X*t i*X⁻¹)=
        (fun i : Fin n => X*Fin.tail t i*X⁻¹) := by funext i; rfl
    simp only [cube]
    rw [he]
    cases hu : u 0
    · simp only [hu,Bool.false_eq_true,↓reduceIte,one_mul]
      exact ih (Fin.tail t) (Fin.tail u)
    · simp only [hu,↓reduceIte]
      rw [←ih (Fin.tail t) (Fin.tail u)]
      group

theorem cube_insert {α ι : Type} {R : ι → FreeGroup α} (n : Nat)
    (t : Fin n → FreeGroup α) (u : Fin n → Bool) (j : Fin n) (z : FreeGroup α) (L : Nat)
    (hu : u j=true) (hc : ∀ i, FiniteArea.Area R (groupComm (t i) z) L) :
    Close R (cube n (Function.update t j (t j*z)) u) (cube n t u*z) (n*L) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    revert hu
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hu
      have ht : Fin.tail (Function.update t 0 (t 0*z))=Fin.tail t := by
        funext i
        simp [Fin.tail,Fin.succ_ne_zero]
      simp only [cube,hu,↓reduceIte,Function.update_self,ht]
      have ha := cube_comm n (Fin.tail t) (Fin.tail u) z L (fun i => hc i.succ)
      have hs : Close R (z*cube n (Fin.tail t) (Fin.tail u)) (cube n (Fin.tail t) (Fin.tail u)*z) (n*L) := by
        have hh := area_inv ha
        simpa [Close,groupComm,mul_inv_rev,mul_assoc] using hh
      have hb := close_left (t 0) hs
      apply close_weaken (by simpa only [mul_assoc] using hb)
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · intro hu
      have h0 : (0:Fin (n+1))≠j.succ := Ne.symm (Fin.succ_ne_zero j)
      have ht : Fin.tail (Function.update t j.succ (t j.succ*z))=
          Function.update (Fin.tail t) j (t j.succ*z) := by
        funext i
        simp [Fin.tail,Function.update_apply]
      simp only [cube,Function.update_of_ne h0,ht]
      have hh := ih (Fin.tail t) (Fin.tail u) j (by exact hu) (fun i => hc i.succ)
      have hb := close_left (if u 0 then t 0 else 1) hh
      have hv : Fin.tail t j=t j.succ := rfl
      rw [hv] at hb
      apply close_weaken (by simpa only [mul_assoc] using hb)
      simp only [Nat.add_mul,Nat.one_mul]
      omega

theorem cube_transvection {α ι : Type} {R : ι → FreeGroup α} (n : Nat) (hn : 1≤n)
    (t : Fin n → FreeGroup α) (i j : Fin n) (X : FreeGroup α) (L : Nat) (hL : 1≤L)
    (hsq : ∀ k, FiniteArea.Area R (t k*t k) 1)
    (hc : ∀ k l, FiniteArea.Area R (groupComm (t k) (t l)) L)
    (hX : ∀ k, Close R (X*t k*X⁻¹) (Function.update t j (t j*t i) k) L)
    (u : Fin n → Bool) (hi : u i=true) (hj : u j=true) :
    Close R (X*cube n t u*X⁻¹) (cube n t (Function.update u i false)) (5*n^2*L) := by
  have h1 := cube_pointwise_close n (fun k => X*t k*X⁻¹) (Function.update t j (t j*t i)) u L hX
  rw [←cube_conjugation] at h1
  have h2 := cube_insert n t u j (t i) L hj (fun k => hc k i)
  have h3 := cube_mul_close n t L hsq hc u (fun k => decide (k=i))
  rw [cube_one_bit] at h3
  have hv : (fun k => u k ^^ decide (k=i))=Function.update u i false := by
    funext k
    by_cases hk : k=i
    · subst k
      simp [hi]
    · simp [hk]
  rw [hv] at h3
  have h := close_trans (close_trans h1 h2) h3
  apply close_weaken h
  have hnn : n≤n^2 := by nlinarith
  have hmul : n*L≤n^2*L := Nat.mul_le_mul_right L hnn
  have hmul1 : n≤n*L := by simpa using Nat.mul_le_mul_left n hL
  nlinarith only [hmul,hmul1]

end Blueprint.PairProof

#print axioms Blueprint.PairProof.cube_pointwise_close
#print axioms Blueprint.PairProof.cube_conjugation
#print axioms Blueprint.PairProof.cube_insert
#print axioms Blueprint.PairProof.cube_transvection
