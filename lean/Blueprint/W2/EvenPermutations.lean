import Blueprint.RatesDefinitions
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def halfSwap (m : Nat) (hm : 0<m) : Equiv.Perm (Fin (2*m)) where
  toFun i := ⟨if i.val<m then i.val+m else i.val-m,by split <;> omega⟩
  invFun i := ⟨if i.val<m then i.val+m else i.val-m,by split <;> omega⟩
  left_inv i := by apply Fin.ext; dsimp; split <;> split <;> omega
  right_inv i := by apply Fin.ext; dsimp; split <;> split <;> omega

theorem halfSwap_val (m : Nat) (hm : 0<m) (i : Fin (2*m)) :
    (halfSwap m hm i).val=(i.val+m)%(2*m) := by
  dsimp [halfSwap]
  split
  · symm; exact Nat.mod_eq_of_lt (by omega)
  · have he : i.val+m=2*m+(i.val-m) := by omega
    rw [he,Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : i.val-m<2*m)]

theorem halfSwap_square (m : Nat) (hm : 0<m) : halfSwap m hm*halfSwap m hm=1 := by
  apply Equiv.ext
  intro i
  exact (halfSwap m hm).left_inv i

def shuffle (m : Nat) (hm : 0<m) : Equiv.Perm (Fin (2*m)) where
  toFun i := ⟨if i.val<m then 2*i.val else 2*(i.val-m)+1,by split <;> omega⟩
  invFun j := ⟨j.val/2+(if j.val%2=0 then 0 else m),by
    have hj := j.isLt
    have hmod := Nat.mod_lt j.val (by decide : 0<2)
    have hdiv := Nat.mod_add_div j.val 2
    split <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt
    dsimp
    split <;> simp_all <;> omega
  right_inv j := by
    apply Fin.ext
    have hj := j.isLt
    have hmod := Nat.mod_lt j.val (by decide : 0<2)
    have hdiv := Nat.mod_add_div j.val 2
    dsimp
    split <;> split <;> omega

theorem shuffle_val (m : Nat) (hm : 0<m) (i : Fin (2*m)) :
    (shuffle m hm i).val=2*(i.val%m)+i.val/m := by
  have hi := i.isLt
  dsimp [shuffle]
  split
  · rw [Nat.mod_eq_of_lt ‹_›,Nat.div_eq_of_lt ‹_›,add_zero]
  · have hdiv : i.val/m=1 := by
      have h1 : 0 < i.val/m := Nat.div_pos (by omega) hm
      have h2 : i.val/m<2 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
      omega
    have hmod := Nat.mod_add_div i.val m
    rw [hdiv,mul_one] at hmod
    rw [hdiv]
    omega

theorem perm_unitary {d : Nat} (p : Equiv.Perm (Fin d)) : IsUnitary (p.permMatrix ℂ) := by
  constructor <;> rw [Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul]
  · simp
  · simp

theorem perm_left {d : Nat} (p : Equiv.Perm (Fin d)) (A : Mat d) (i j : Fin d) :
    (p.permMatrix ℂ*A) i j=A (p i) j := by
  rw [Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_mul]
  rfl

theorem perm_right {d : Nat} (p : Equiv.Perm (Fin d)) (A : Mat d) (i j : Fin d) :
    (A*p.permMatrix ℂ) i j=A i (p.symm j) := by
  rw [Equiv.Perm.permMatrix,PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem perm_diagonal_conjugation {d : Nat} (p : Equiv.Perm (Fin d)) (v : Fin d → ℂ) :
    p.permMatrix ℂ*Matrix.diagonal v*(p.permMatrix ℂ).conjTranspose=Matrix.diagonal (fun i => v (p i)) := by
  ext i j
  rw [Matrix.conjTranspose_permMatrix,perm_right,perm_left]
  change Matrix.diagonal v (p i) (p j)=Matrix.diagonal (fun i => v (p i)) i j
  by_cases hij : i=j
  · subst j; simp
  · simp [Matrix.diagonal_apply, p.injective.ne hij,hij]

end
end Blueprint.W2
