import Blueprint.A.HoughtonCollectionWords

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
open scoped BigOperators
set_option maxHeartbeats 1000000

def collectionState (m l : ℤ) : FreeGroup (Fin 3) := johnsonP^m*johnsonQ^l
def collectionCost (M l : Nat) : Nat := l+∑ i∈Finset.range l,(uniformFarCap M+1)*i^2

theorem collect_p (M : Nat) (hM : 2≤M) (m : ℤ) (l : Nat) (hl : l≤M) :
    Close johnsonFiniteRelator (collectionState m l*johnsonP)
      (sigmaValue (sigmaDescendingWord m false l)*collectionState (m+1) l) (collectionCost M l) := by
  have hq := close_trans (qConjP_expansion l)
    (close_right johnsonP (qInverseDescending_close M hM l hl))
  have h := close_left (johnsonP^m) (close_right (johnsonQ^l) hq)
  convert h using 1
  · dsimp [collectionState]; simp only [zpow_natCast]; group
  · rw [←sigmaDescendingWord_shift_value]
    dsimp [collectionState]
    simp only [zpow_add,zpow_one,zpow_natCast]
    group
  · rfl

theorem collect_p_inverse (M : Nat) (hM : 2≤M) (m : ℤ) (l : Nat) (hl : l≤M) :
    Close johnsonFiniteRelator (collectionState m l*johnsonP⁻¹)
      (sigmaValue (sigmaInverseWord (sigmaDescendingWord (m-1) false l))*
        collectionState (m-1) l) (collectionCost M l) := by
  have h := close_right johnsonP⁻¹
    (close_left (sigmaValue (sigmaDescendingWord (m-1) false l))⁻¹
      (close_symm (collect_p M hM (m-1) l hl)))
  simpa only [sub_add_cancel,sigmaValue_inverse,inv_mul_cancel_left,mul_inv_cancel_right,
    mul_assoc,mul_inv_cancel,mul_one] using h

theorem collect_alpha (M : Nat) (hM : 2≤M) (m : ℤ) (l : Nat) (hl : l≤M) :
    Close johnsonFiniteRelator (collectionState m l*johnsonAlpha)
      (sigmaZ (m+l)*collectionState m l) ((uniformFarCap M+1)*l^2) := by
  have h := close_right (collectionState m l) (close_conj (johnsonP^m) (qSigma_uniform_close M hM l hl))
  convert h using 1
  · dsimp [collectionState,qSigma]; simp only [zpow_natCast]; group
  · rw [←sigmaZ_shift]

theorem collect_alpha_inverse (M : Nat) (hM : 2≤M) (m : ℤ) (l : Nat) (hl : l≤M) :
    Close johnsonFiniteRelator (collectionState m l*johnsonAlpha⁻¹)
      ((sigmaZ (m+l))⁻¹*collectionState m l) ((uniformFarCap M+1)*l^2) := by
  have h := close_right (collectionState m l)
    (close_conj (johnsonP^m) (close_inv (qSigma_uniform_close M hM l hl)))
  convert h using 1
  · dsimp [collectionState,qSigma]; simp only [zpow_natCast]; group
  · rw [sigmaZ_shift]; group

theorem collectionCost_le (M n l : Nat) (hn : 1≤n) (hl : l≤2*n) :
    collectionCost M l≤10*(uniformFarCap M+1)*n^3 := by
  have hs : (∑ i∈Finset.range l,(uniformFarCap M+1)*i^2)≤l*((uniformFarCap M+1)*l^2) := by
    calc
      _ ≤ ∑ _i∈Finset.range l,(uniformFarCap M+1)*l^2 := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        exact Nat.le_of_lt (Finset.mem_range.mp hi)
      _ = _ := by simp
  have hc : l^3≤(2*n)^3 := Nat.pow_le_pow_left hl 3
  have hn2 : 1≤n^2 := by nlinarith
  have hn3 : n≤n^3 := by nlinarith
  have hF : 1≤uniformFarCap M+1 := by omega
  have hp := Nat.mul_le_mul_left (uniformFarCap M+1) hc
  have hnF := Nat.mul_le_mul_left (n^3) hF
  dsimp [collectionCost]
  nlinarith

theorem collectionAlphaCost_le (M n l : Nat) (hn : 1≤n) (hl : l≤2*n) :
    (uniformFarCap M+1)*l^2≤10*(uniformFarCap M+1)*n^3 := by
  have hl2 : l^2≤(2*n)^2 := Nat.pow_le_pow_left hl 2
  have hn2 : n^2≤n^3 := by
    have h : n^2≤n^2*n := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have hp := Nat.mul_le_mul_left (uniformFarCap M+1) hl2
  have hq := Nat.mul_le_mul_left (uniformFarCap M+1) hn2
  nlinarith

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.collectionState
#print axioms Blueprint.HoughtonProof.collectionCost
#print axioms Blueprint.HoughtonProof.collect_p
#print axioms Blueprint.HoughtonProof.collect_p_inverse
#print axioms Blueprint.HoughtonProof.collect_alpha
#print axioms Blueprint.HoughtonProof.collect_alpha_inverse
#print axioms Blueprint.HoughtonProof.collectionCost_le
#print axioms Blueprint.HoughtonProof.collectionAlphaCost_le
