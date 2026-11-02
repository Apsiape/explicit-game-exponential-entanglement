import Blueprint.A.HoughtonCollection

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem sigma_far_area (M : Nat) (hM : 2≤M) (i j : Nat)
    (hij : i+2≤j) (hj : j≤M) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ i) (sigmaZ j)) (uniformFarCap M+1) := by
  have h := far_uniform_translate_area M hM (i:ℤ) (j-i) (by omega) (by omega)
  have he : (i:ℤ)+(j-i:Nat)=j := by omega
  rw [he] at h
  exact area_weaken h (by omega)

theorem sigma_far_swap (M : Nat) (hM : 2≤M) (i j : Nat)
    (hij : i+2≤j) (hj : j≤M) :
    Close johnsonFiniteRelator (sigmaZ j*sigmaZ i) (sigmaZ i*sigmaZ j) (uniformFarCap M+1) := by
  simpa only [Close,groupComm,mul_inv_rev,mul_assoc] using
    area_comm_swap (sigma_far_area M hM i j hij hj)

theorem sigma_braid_close (i : Nat) :
    Close johnsonFiniteRelator (sigmaZ (i+1:Nat)*sigmaZ i*sigmaZ (i+1:Nat))
      (sigmaZ i*sigmaZ (i+1:Nat)*sigmaZ i) 4 := by
  have h := close_symm (sigmaZ_braid (i:ℤ))
  simpa only [Close,Nat.cast_add,Nat.cast_one,mul_inv_rev,inv_inv,mul_assoc] using h

def coxCoset (K k : Nat) : FreeGroup (Fin 3) := sigmaDescending (k:ℤ) (K-k)

theorem coxCoset_self (K : Nat) : coxCoset K K=1 := by simp [coxCoset,sigmaDescending]

theorem coxCoset_split (K k : Nat) (hk : k<K) :
    coxCoset K k=coxCoset K (k+1)*sigmaZ k := by
  have he : K-k=(K-(k+1))+1 := by omega
  change sigmaDescending (k:ℤ) (K-k)=sigmaDescending ((k+1:Nat):ℤ) (K-(k+1))*sigmaZ k
  rw [he,sigmaDescending_split]
  simp [sigmaDescending]

theorem coxCoset_top (K k : Nat) (hk : k≤K) :
    coxCoset (K+1) k=sigmaZ K*coxCoset K k := by
  have he : K+1-k=(K-k)+1 := by omega
  have hz : (k:ℤ)+(K-k:Nat)=K := by omega
  simp only [coxCoset,he,sigmaDescending,hz]

theorem coxCoset_far_low (M : Nat) (hM : 2≤M) (K k i : Nat)
    (hk : k≤K) (hK : K≤M+1) (hi : i+2≤k) :
    Close johnsonFiniteRelator (coxCoset K k*sigmaZ i) (sigmaZ i*coxCoset K k)
      ((K-k)*(uniformFarCap M+1)) := by
  have h : FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ i) (coxCoset K k))
      ((K-k)*(uniformFarCap M+1)) := by
    unfold coxCoset
    convert descending_comm_area (k:ℤ) (K-k) (sigmaZ i) (fun _ => uniformFarCap M+1) ?_ using 1
    · simp
    · intro j hj
      have ht := sigma_far_area M hM i (k+j) (by omega) (by omega)
      simpa only [Nat.cast_add] using ht
  simpa only [Close,groupComm,mul_inv_rev,mul_assoc] using area_comm_swap h

theorem coxCoset_far_high (M : Nat) (hM : 2≤M) (K k i : Nat)
    (hk : k≤K) (hK : K≤M+1) (hi : K+1 ≤ i) (hiM : i≤M) :
    Close johnsonFiniteRelator (coxCoset K k*sigmaZ i) (sigmaZ i*coxCoset K k)
      ((K-k)*(uniformFarCap M+1)) := by
  have h : FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ i) (coxCoset K k))
      ((K-k)*(uniformFarCap M+1)) := by
    unfold coxCoset
    convert descending_comm_area (k:ℤ) (K-k) (sigmaZ i) (fun _ => uniformFarCap M+1) ?_ using 1
    · simp
    · intro j hj
      have ht := area_comm_swap (sigma_far_area M hM (k+j) i (by omega) hiM)
      simpa only [Nat.cast_add] using ht
  simpa only [Close,groupComm,mul_inv_rev,mul_assoc] using area_comm_swap h

theorem coxCoset_cancel (K k : Nat) (hk : k<K) :
    Close johnsonFiniteRelator (coxCoset K k*sigmaZ k) (coxCoset K (k+1)) 1 := by
  have h := close_left (coxCoset K (k+1)) (close_to_one.mpr (sigmaZ_square (k:ℤ)))
  simpa only [coxCoset_split K k hk,mul_one,mul_assoc] using h

theorem coxCoset_extend (K k : Nat) (hk : 1≤k) (hkK : k≤K) :
    coxCoset K k*sigmaZ (k-1:Nat)=coxCoset K (k-1) := by
  simpa only [show k-1+1=k by omega] using (coxCoset_split K (k-1) (by omega)).symm

/-- The last insertion rule is a charged braid with the required far
commutations. Its cost is bounded at every finite symmetric-group level. -/
theorem coxCoset_insert_high (M : Nat) (hM : 2≤M) (K : Nat) :
    ∀ k i : Nat, k+1 ≤ i → i<K → K≤M+1 →
      Close johnsonFiniteRelator (coxCoset K k*sigmaZ i)
        (sigmaZ (i-1:Nat)*coxCoset K k) (4*(uniformFarCap M+1)*K) := by
  induction K with
  | zero => intro k i hk hi; omega
  | succ K ih =>
    intro k i hki hi hK
    by_cases hiK : i<K
    · have h1 := close_left (sigmaZ K) (ih k i hki hiK (by omega))
      have h2 := close_right (coxCoset K k)
        (sigma_far_swap M hM (i-1) K (by omega) (by omega))
      have h := close_trans h1 (by simpa only [mul_assoc] using h2)
      apply close_weaken (by simpa only [coxCoset_top K k (by omega),mul_assoc] using h)
      nlinarith
    · have he : i=K := by omega
      subst i
      have hkK : k≤K-1 := by omega
      have h1 := close_left (sigmaZ K*sigmaZ (K-1:Nat))
        (coxCoset_far_high M hM (K-1) k K hkK (by omega) (by omega) (by omega))
      have h2 := close_right (coxCoset (K-1) k) (sigma_braid_close (K-1))
      have hc : coxCoset K k=sigmaZ (K-1:Nat)*coxCoset (K-1) k := by
        simpa only [show K-1+1=K by omega] using coxCoset_top (K-1) k hkK
      have h : Close johnsonFiniteRelator (coxCoset (K+1) k*sigmaZ K)
          (sigmaZ (K-1:Nat)*coxCoset (K+1) k)
          (((K-1)-k)*(uniformFarCap M+1)+4) := by
        convert close_trans h1 (by simpa only [show K-1+1=K by omega,mul_assoc] using h2) using 1
        all_goals simp only [coxCoset_top K k (by omega),hc,mul_assoc]
      apply close_weaken h
      have hF : 1≤uniformFarCap M+1 := by omega
      have hb : (K-1-k)*(uniformFarCap M+1)≤K*(uniformFarCap M+1) := Nat.mul_le_mul_right _ (by omega)
      nlinarith

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.sigma_far_area
#print axioms Blueprint.HoughtonProof.sigma_far_swap
#print axioms Blueprint.HoughtonProof.sigma_braid_close
#print axioms Blueprint.HoughtonProof.coxCoset
#print axioms Blueprint.HoughtonProof.coxCoset_self
#print axioms Blueprint.HoughtonProof.coxCoset_split
#print axioms Blueprint.HoughtonProof.coxCoset_top
#print axioms Blueprint.HoughtonProof.coxCoset_far_low
#print axioms Blueprint.HoughtonProof.coxCoset_far_high
#print axioms Blueprint.HoughtonProof.coxCoset_cancel
#print axioms Blueprint.HoughtonProof.coxCoset_extend
#print axioms Blueprint.HoughtonProof.coxCoset_insert_high
