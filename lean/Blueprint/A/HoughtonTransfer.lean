import Blueprint.A.HoughtonEta

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
open scoped BigOperators
set_option maxHeartbeats 1000000

def etaBound (A : Nat → Nat) (i : Nat) : Nat := 2*i+1+∑ l∈Finset.range i,A (i-l+1)
def transferBound (A : Nat → Nat) (j : Nat) : Nat := ∑ l∈Finset.range j,etaBound A l
def negativeBound (A : Nat → Nat) (k : Nat) : Nat := 2*k+5+∑ l∈Finset.range (k-2),A (l+2)
def qSigma (j : Nat) : FreeGroup (Fin 3) := johnsonQ^j*johnsonAlpha*(johnsonQ^j)⁻¹
def pConjQ (k : Nat) : FreeGroup (Fin 3) := johnsonP^(k:ℤ)*johnsonQ*(johnsonP^(k:ℤ))⁻¹

theorem qSigma_succ (j : Nat) : qSigma (j+1)=johnsonQ*qSigma j*johnsonQ⁻¹ := by
  simp only [qSigma,pow_succ']
  group

theorem q_sigma_step_close (j k : Nat)
    (h : FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ j) (etaZ 0)) k) :
    Close johnsonFiniteRelator (johnsonQ*sigmaZ j*johnsonQ⁻¹) (sigmaZ (j+1:Nat)) k := by
  have hs : sigmaZ (j+1:Nat)=johnsonP*sigmaZ j*johnsonP⁻¹ := by
    have hh := sigmaZ_shift 1 (j:ℤ)
    rw [show (1:ℤ)+(j:ℤ)=((j+1:Nat):ℤ) by omega] at hh
    simpa only [zpow_one] using hh
  convert area_conj johnsonQ h using 1
  rw [hs,etaZ_zero]
  dsimp [Close,groupComm]
  group

/-- Lee recursion (ii), with the exact sum of the previously constructed
eta-commutator areas and no presentation-completeness assumption. -/
theorem qSigma_close (j : Nat) (A : Nat → Nat)
    (hA : ∀ m, 2≤m → m≤j →
      FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ m)) (A m)) :
    Close johnsonFiniteRelator (qSigma j) (sigmaZ j) (transferBound A j) := by
  induction j with
  | zero => simpa [qSigma,sigmaZ,transferBound] using close_refl johnsonFiniteRelator johnsonAlpha
  | succ j ih =>
    have hp := ih (fun m hm hj => hA m hm (by omega))
    have he := eta_comm_area j A (fun m hm hj => hA m hm (by omega))
    have h := close_trans (close_conj johnsonQ hp) (q_sigma_step_close j (etaBound A j) he)
    simpa only [qSigma_succ,transferBound,Finset.sum_range_succ] using h

theorem pConjQ_step (k : Nat) :
    Close johnsonFiniteRelator (pConjQ (k+1)) (sigmaZ k*pConjQ k) 1 := by
  have h := close_conj (johnsonP^(k:ℤ)) johnson_pq_close
  convert h using 1
  all_goals
    dsimp [pConjQ,sigmaZ,Close]
    try simp only [zpow_add,zpow_one]
    group

theorem pConjQ_expansion (k : Nat) :
    Close johnsonFiniteRelator (pConjQ k) (sigmaDescending 0 k*johnsonQ) k := by
  induction k with
  | zero => simpa [pConjQ,sigmaDescending] using close_refl johnsonFiniteRelator johnsonQ
  | succ k ih =>
    have h := close_trans (pConjQ_step k) (close_left (sigmaZ k) ih)
    simpa only [sigmaDescending,zero_add,mul_assoc,Nat.add_comm] using h

/-- The five-cell terminal word in Lee recursion (iii). -/
theorem alpha_near_q_area :
    FiniteArea.Area johnsonFiniteRelator
      (groupComm (sigmaZ 0) (sigmaZ 1*sigmaZ 0*johnsonQ)) 5 := by
  have hq := q_sigma_step_close 0 1 (by simpa only [Nat.cast_zero,sigmaZ_zero] using alpha_eta_area)
  have hi := close_inv hq
  have hc := close_right ((sigmaZ 0)⁻¹*(sigmaZ 1)⁻¹)
    (close_left (sigmaZ 0*sigmaZ 1*sigmaZ 0) hi)
  have ht : Close johnsonFiniteRelator
      (groupComm (sigmaZ 0) (sigmaZ 1*sigmaZ 0*johnsonQ))
      (sigmaZ 0*sigmaZ 1*sigmaZ 0*(sigmaZ 1)⁻¹*(sigmaZ 0)⁻¹*(sigmaZ 1)⁻¹) 1 := by
    convert hc using 1
    · dsimp [groupComm]
      group
    · simp only [Nat.zero_add]
      group
  exact close_to_one.mp (close_trans ht (close_to_one.mpr sigmaZ_braid_zero))

/-- Lee recursion (iii), retaining the original 2k+5 and far-cell sum. -/
theorem negative_q_comm_area (k : Nat) (hk : 2≤k) (A : Nat → Nat)
    (hA : ∀ m, 2≤m → m<k →
      FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ m)) (A m)) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ (-(k:ℤ))) johnsonQ) (negativeBound A k) := by
  have ht : FiniteArea.Area johnsonFiniteRelator
      (groupComm (sigmaZ 0) (sigmaDescending 2 (k-2)))
      (∑ l∈Finset.range (k-2),A (l+2)) := by
    apply descending_comm_area
    intro l hl
    have h := hA (l+2) (by omega) (by omega)
    simpa only [Nat.cast_add,Nat.cast_ofNat,add_comm] using h
  have hr := area_comm_right_mul ht alpha_near_q_area
  have hs : sigmaDescending 0 k*johnsonQ =
      sigmaDescending 2 (k-2)*(sigmaZ 1*sigmaZ 0*johnsonQ) := by
    rw [show k=(k-2)+2 by omega,sigmaDescending_split]
    simp only [sigmaDescending,zero_add,Nat.cast_zero,Nat.cast_one,mul_one,mul_assoc]
    norm_num
  have hc := close_comm (close_refl johnsonFiniteRelator (sigmaZ 0)) (pConjQ_expansion k)
  rw [hs] at hc
  have h := area_conj (johnsonP^(-(k:ℤ)))
    (close_to_one.mp (close_trans hc (close_to_one.mpr hr)))
  convert h using 1
  · dsimp [sigmaZ,pConjQ,groupComm]
    simp only [zpow_zero,one_mul,mul_one,zpow_neg]
    group
  · dsimp [negativeBound]
    omega

theorem comm_conjugate_power_area {α ι : Type} {R : ι → FreeGroup α}
    {a b c : FreeGroup α} {A B : Nat}
    (hA : FiniteArea.Area R (groupComm a c) A)
    (hB : FiniteArea.Area R (groupComm a b) B) (j : Nat) :
    FiniteArea.Area R (groupComm a (b^j*c*(b^j)⁻¹)) (2*j*B+A) := by
  have hb := area_comm_right_pow hB j
  have hs : Close R ((b^j)⁻¹*a*b^j) a (j*B) := by
    convert area_conj (b^j)⁻¹ hb using 1
    dsimp [Close,groupComm]
    group
  have hc := close_comm hs (close_refl R c)
  have h := area_conj (b^j) (close_to_one.mp (close_trans hc (close_to_one.mpr hA)))
  convert h using 1
  · dsimp [groupComm]
    group
  · ring

/-- Lee recursion (iv): halving a far commutator costs precisely the
previous far area, 2j negative-ray commutations and two transfer replacements. -/
theorem far_transfer_area (k j A B U : Nat)
    (hA : FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ k)) A)
    (hB : FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ (-(k:ℤ))) johnsonQ) B)
    (hU : Close johnsonFiniteRelator (qSigma j) (sigmaZ j) U) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ (k+j:Nat)))
      (A+2*j*B+2*U) := by
  have ha := far_area_translate (-(k:ℤ)) 0 A (by simpa only [zero_sub,neg_neg] using hA)
  have hr := comm_conjugate_power_area ha hB j
  have hc := close_comm (close_refl johnsonFiniteRelator (sigmaZ (-(k:ℤ)))) (close_symm hU)
  have h := close_to_one.mp (close_trans hc (close_to_one.mpr hr))
  have hh := comm_conjugate_area h (johnsonP^(k:ℤ))
  rw [←sigmaZ_shift,←sigmaZ_shift] at hh
  simpa only [add_neg_cancel,Nat.cast_add,Nat.zero_mul,Nat.mul_zero,Nat.zero_add,qSigma,
    show 2*U+(2*j*B+A)=A+2*j*B+2*U by omega] using hh

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.etaBound
#print axioms Blueprint.HoughtonProof.transferBound
#print axioms Blueprint.HoughtonProof.negativeBound
#print axioms Blueprint.HoughtonProof.qSigma
#print axioms Blueprint.HoughtonProof.pConjQ
#print axioms Blueprint.HoughtonProof.qSigma_succ
#print axioms Blueprint.HoughtonProof.q_sigma_step_close
#print axioms Blueprint.HoughtonProof.qSigma_close
#print axioms Blueprint.HoughtonProof.pConjQ_step
#print axioms Blueprint.HoughtonProof.pConjQ_expansion
#print axioms Blueprint.HoughtonProof.alpha_near_q_area
#print axioms Blueprint.HoughtonProof.negative_q_comm_area
#print axioms Blueprint.HoughtonProof.comm_conjugate_power_area
#print axioms Blueprint.HoughtonProof.far_transfer_area
