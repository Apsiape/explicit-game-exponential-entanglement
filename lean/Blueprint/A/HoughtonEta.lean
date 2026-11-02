import Blueprint.A.HoughtonCells

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem area_comm_swap {α ι : Type} {R : ι → FreeGroup α}
    {a b : FreeGroup α} {k : Nat} (h : FiniteArea.Area R (groupComm a b) k) :
    FiniteArea.Area R (groupComm b a) k := by
  simpa [groupComm,mul_inv_rev,mul_assoc] using area_inv h

theorem area_comm_right_mul {α ι : Type} {R : ι → FreeGroup α}
    {a b c : FreeGroup α} {k l : Nat}
    (hb : FiniteArea.Area R (groupComm a b) k) (hc : FiniteArea.Area R (groupComm a c) l) :
    FiniteArea.Area R (groupComm a (b*c)) (k+l) :=
  area_comm_swap (area_comm_mul (area_comm_swap hb) (area_comm_swap hc))

theorem area_comm_right_pow {α ι : Type} {R : ι → FreeGroup α}
    {a b : FreeGroup α} {k : Nat} (h : FiniteArea.Area R (groupComm a b) k) (n : Nat) :
    FiniteArea.Area R (groupComm a (b^n)) (n*k) := by
  induction n with
  | zero => simpa [groupComm] using area_one R 0
  | succ n ih =>
    simpa only [pow_succ,Nat.add_mul,Nat.one_mul] using area_comm_right_mul ih h

theorem comm_conjugate_area {α ι : Type} {R : ι → FreeGroup α}
    {a b : FreeGroup α} {k : Nat} (h : FiniteArea.Area R (groupComm a b) k)
    (g : FreeGroup α) :
    FiniteArea.Area R (groupComm (g*a*g⁻¹) (g*b*g⁻¹)) k := by
  convert area_conj g h using 1
  dsimp [groupComm]
  group

theorem far_area_translate (i j : ℤ) (k : Nat)
    (h : FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ (j-i))) k) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ i) (sigmaZ j)) k := by
  have ht := comm_conjugate_area h (johnsonP^i)
  rw [←sigmaZ_shift,←sigmaZ_shift] at ht
  simpa only [add_zero,add_sub_cancel] using ht

def sigmaDescending (a : ℤ) : Nat → FreeGroup (Fin 3)
  | 0 => 1
  | n+1 => sigmaZ (a+n)*sigmaDescending a n

theorem sigmaDescending_split (a : ℤ) (m n : Nat) :
    sigmaDescending a (m+n)=sigmaDescending (a+n) m*sigmaDescending a n := by
  induction m with
  | zero => simp [sigmaDescending]
  | succ m ih =>
    rw [show m+1+n=(m+n)+1 by omega,sigmaDescending,ih,sigmaDescending]
    rw [Nat.cast_add]
    simp only [add_assoc,add_comm,add_left_comm,mul_assoc]

theorem eta_expansion_close (n : Nat) :
    Close johnsonFiniteRelator (etaZ 0) (etaZ n*sigmaDescending (-1) n) n := by
  induction n with
  | zero => simpa [sigmaDescending] using close_refl johnsonFiniteRelator (etaZ 0)
  | succ n ih =>
    have h := close_right (sigmaDescending (-1) n) (etaZ_step (n : ℤ))
    have ht := close_trans ih h
    simpa only [sigmaDescending,Nat.cast_add,Nat.cast_one,
      show (-1:ℤ)+(n:ℤ)=(n:ℤ)-1 by omega,mul_assoc] using ht

theorem sigma_eta_same_index_area (i : ℤ) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ i) (etaZ i)) 1 := by
  have h := comm_conjugate_area (by simpa only [sigmaZ_zero] using alpha_eta_area) (johnsonP^i)
  rw [←etaZ_shift] at h
  simpa only [add_zero,sigmaZ] using h

theorem descending_comm_area (a : ℤ) (n : Nat) (g : FreeGroup (Fin 3)) (A : Nat → Nat)
    (h : ∀ l<n, FiniteArea.Area johnsonFiniteRelator (groupComm g (sigmaZ (a+l))) (A l)) :
    FiniteArea.Area johnsonFiniteRelator (groupComm g (sigmaDescending a n))
      (∑ l∈Finset.range n,A l) := by
  induction n with
  | zero => simpa [sigmaDescending,groupComm] using area_one johnsonFiniteRelator 0
  | succ n ih =>
    have ht := ih (fun l hl => h l (by omega))
    have hh := area_comm_right_mul (h n (by omega)) ht
    simpa only [sigmaDescending,Finset.sum_range_succ,Nat.add_comm] using hh

/-- Lee recursion (i): its area witnesses are built from strictly shorter far
commutator witnesses; there is no global filling or presentation premise. -/
theorem eta_comm_area (i : Nat) (A : Nat → Nat)
    (hA : ∀ m, 2≤m → m ≤ i+1 →
      FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ m)) (A m)) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ i) (etaZ 0))
      (2*i+1+∑ l∈Finset.range i,A (i-l+1)) := by
  have ht : FiniteArea.Area johnsonFiniteRelator
      (groupComm (sigmaZ i) (sigmaDescending (-1) i)) (∑ l∈Finset.range i,A (i-l+1)) := by
    apply descending_comm_area
    intro l hl
    have hd : (i:ℤ)-((-1:ℤ)+(l:ℤ))=((i-l+1:Nat):ℤ) := by omega
    have hfar := hA (i-l+1) (by omega) (by omega)
    have hf := far_area_translate ((-1:ℤ)+(l:ℤ)) (i:ℤ) (A (i-l+1)) (by simpa only [hd] using hfar)
    exact area_comm_swap hf
  have hc := close_comm (close_refl johnsonFiniteRelator (sigmaZ i)) (eta_expansion_close i)
  have hr := area_comm_right_mul (sigma_eta_same_index_area i) ht
  have h := close_to_one.mp (close_trans hc (close_to_one.mpr hr))
  convert h using 1 <;> omega

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.area_comm_swap
#print axioms Blueprint.HoughtonProof.area_comm_right_mul
#print axioms Blueprint.HoughtonProof.area_comm_right_pow
#print axioms Blueprint.HoughtonProof.comm_conjugate_area
#print axioms Blueprint.HoughtonProof.far_area_translate
#print axioms Blueprint.HoughtonProof.sigmaDescending
#print axioms Blueprint.HoughtonProof.sigmaDescending_split
#print axioms Blueprint.HoughtonProof.eta_expansion_close
#print axioms Blueprint.HoughtonProof.sigma_eta_same_index_area
#print axioms Blueprint.HoughtonProof.descending_comm_area
#print axioms Blueprint.HoughtonProof.eta_comm_area
