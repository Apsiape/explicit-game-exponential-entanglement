import Blueprint.A.HoughtonFar
import Mathlib.Algebra.BigOperators.Intervals

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem etaBound_le (A : Nat → Nat) (i M : Nat)
    (hA : ∀ m, 2≤m → m ≤ i+1 → A m≤M) : etaBound A i≤2*i+1+i*M := by
  unfold etaBound
  apply Nat.add_le_add_left
  calc
    (∑ l∈Finset.range i,A (i-l+1)) ≤ ∑ _l∈Finset.range i,M := by
      apply Finset.sum_le_sum
      intro l hl
      have hl' := Finset.mem_range.mp hl
      exact hA (i-l+1) (by omega) (by omega)
    _ = i*M := by simp

theorem sum_odds (j : Nat) : (∑ l∈Finset.range j,(2*l+1))=j^2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ,ih]
    ring

theorem twice_transferBound_le (A : Nat → Nat) (j M : Nat)
    (hA : ∀ m, 2≤m → m≤j → A m≤M) :
    2*transferBound A j≤2*j^2+j*(j-1)*M := by
  have ht : transferBound A j≤∑ l∈Finset.range j,(2*l+1+l*M) := by
    apply Finset.sum_le_sum
    intro l hl
    have hl' := Finset.mem_range.mp hl
    exact etaBound_le A l M (fun m hm hml => hA m hm (by omega))
  have he : 2*(∑ l∈Finset.range j,(2*l+1+l*M))=2*j^2+j*(j-1)*M := by
    rw [Finset.sum_add_distrib,sum_odds,←Finset.sum_mul]
    calc
      2*(j^2+(∑ l∈Finset.range j,l)*M)=2*j^2+((∑ l∈Finset.range j,l)*2)*M := by ring
      _ = _ := by rw [Finset.sum_range_id_mul_two]
  exact he ▸ Nat.mul_le_mul_left 2 ht

theorem negativeBound_le (A : Nat → Nat) (k M : Nat) (hk : 2≤k)
    (hA : ∀ m, 2≤m → m<k → A m≤M) :
    negativeBound A k≤2*k+5+(k-2)*M := by
  unfold negativeBound
  apply Nat.add_le_add_left
  calc
    (∑ l∈Finset.range (k-2),A (l+2))≤∑ _l∈Finset.range (k-2),M := by
      apply Finset.sum_le_sum
      intro l hl
      have hl' := Finset.mem_range.mp hl
      exact hA (l+2) (by omega) (by omega)
    _ = (k-2)*M := by simp

theorem halving_cost_bound (A : Nat → Nat) (k j M : Nat)
    (hk : 2≤k) (hj : 1≤j) (hjk : j≤k)
    (hA : ∀ m, 2≤m → m≤k → A m≤M) :
    A k+2*j*negativeBound A k+2*transferBound A j+4≤3*k^2*(M+4) := by
  have ha := hA k hk le_rfl
  have hb := negativeBound_le A k M hk (fun m hm hmk => hA m hm (by omega))
  have hu := twice_transferBound_le A j M (fun m hm hmj => hA m hm (le_trans hmj hjk))
  have hs := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ha
    (Nat.mul_le_mul_left (2*j) hb)) hu) 4
  calc
    A k+2*j*negativeBound A k+2*transferBound A j+4
      ≤ M+2*j*(2*k+5+(k-2)*M)+(2*j^2+j*(j-1)*M)+4 := hs
    _ ≤ M+2*k*(2*k+5+(k-2)*M)+(2*k^2+k*(k-1)*M)+4 := by gcongr
    _ ≤ 3*k^2*(M+4) := by
      obtain ⟨z,rfl⟩ : ∃ z, k=z+2 := ⟨k-2,by omega⟩
      rw [Nat.add_sub_cancel,show z+2-1=z+1 by omega]
      ring_nf
      omega

def dyadicCap (h : Nat) : Nat := 5*3^h*2^(h*(h+1))

theorem dyadicCap_zero : dyadicCap 0=5 := by norm_num [dyadicCap]

theorem dyadicCap_ge_five (h : Nat) : 5≤dyadicCap h := by
  have h3 : 1≤3^h := Nat.pow_pos (by decide : 0<3)
  have h2 : 1≤2^(h*(h+1)) := Nat.pow_pos (by decide : 0<2)
  dsimp [dyadicCap]
  nlinarith

theorem dyadicCap_succ (h : Nat) :
    dyadicCap (h+1)=3*(2^(h+1))^2*dyadicCap h := by
  have hp : (2:Nat)^((h+1)*(h+1+1))=(2^(h+1))^2*2^(h*(h+1)) := by
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  unfold dyadicCap
  rw [hp,pow_succ (3:Nat) h]
  ring

/-- The exact dyadic estimate of Appendix A, Proposition A.3. The additional
four units are the same offset used to close the paper's halving recursion. -/
theorem farAreaBound_dyadic (h : Nat) : ∀ n : Nat, 2≤n → n≤2^(h+1) →
    farAreaBound n+4≤dyadicCap h := by
  induction h with
  | zero =>
    intro n hn hb
    have he : n=2 := by norm_num at hb; omega
    subst n
    rw [farAreaBound_small 2 (by omega),dyadicCap_zero]
  | succ h ih =>
    intro n hn hb
    by_cases hs : n≤2
    · rw [farAreaBound_small n hs]
      exact dyadicCap_ge_five (h+1)
    · let k := (n+1)/2
      let j := n-k
      have hij := halving_indices n (by omega)
      change 2≤k ∧ 1≤j ∧ j≤k ∧ k<n ∧ j<n ∧ k+j=n at hij
      have hpow : 2^(h+1+1)=2*2^(h+1) := by rw [pow_succ]; omega
      have hk : k≤2^(h+1) := by
        rw [show h+1+1=(h+1)+1 by omega,pow_succ] at hb
        dsimp [k]
        omega
      let M := dyadicCap h-4
      have hcap := dyadicCap_ge_five h
      have hm : M+4=dyadicCap h := by dsimp [M]; omega
      have ha : ∀ m, 2≤m → m≤k → farAreaBound m≤M := by
        intro m hm' hmk
        have hi := ih m hm' (le_trans hmk hk)
        dsimp [M]
        omega
      rw [farAreaBound_step n (by omega)]
      calc
        farAreaBound k+2*j*negativeBound farAreaBound k+2*transferBound farAreaBound j+4
          ≤ 3*k^2*(M+4) := halving_cost_bound farAreaBound k j M hij.1 hij.2.1 hij.2.2.1 ha
        _ = 3*k^2*dyadicCap h := by rw [hm]
        _ ≤ 3*(2^(h+1))^2*dyadicCap h := by gcongr
        _ = dyadicCap (h+1) := (dyadicCap_succ h).symm

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.etaBound_le
#print axioms Blueprint.HoughtonProof.sum_odds
#print axioms Blueprint.HoughtonProof.twice_transferBound_le
#print axioms Blueprint.HoughtonProof.negativeBound_le
#print axioms Blueprint.HoughtonProof.halving_cost_bound
#print axioms Blueprint.HoughtonProof.dyadicCap
#print axioms Blueprint.HoughtonProof.dyadicCap_zero
#print axioms Blueprint.HoughtonProof.dyadicCap_ge_five
#print axioms Blueprint.HoughtonProof.dyadicCap_succ
#print axioms Blueprint.HoughtonProof.farAreaBound_dyadic
