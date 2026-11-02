import Companion.ReturnSequentialBounds

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 600000

theorem nu_one : nu 1=3 := by norm_num [nu]

theorem nu_succ (n : Nat) : nu (n+1)=nu n+3*((n:ℝ)-1)+13/Real.sqrt 2 := by
  unfold nu
  push_cast
  ring

theorem nu_mono {r s : Nat} (hr : 1≤r) (hrs : r≤s) : nu r≤nu s := by
  induction s,hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hs ih =>
    rw [nu_succ]
    have h1 : (1:ℝ)≤s := by exact_mod_cast (hr.trans hs)
    have hp : 0≤13/Real.sqrt 2 := by positivity
    linarith

theorem nu_nonneg {n : Nat} (hn : 1≤n) : 0≤nu n := by
  have h := nu_mono (by omega : 1≤1) hn
  rw [nu_one] at h
  linarith

theorem sum_nu_mono {r s : Nat} (hrs : r≤s) :
    (∑ l ∈ Finset.range r, nu (l+1))≤∑ l ∈ Finset.range s, nu (l+1) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrs)
    (fun l _ _ => nu_nonneg (by omega))

theorem returnConstant_nonneg (s : Nat) : 0≤returnConstant s := by
  unfold returnConstant
  positivity

theorem returnConstant_pos {s : Nat} (hs : 1≤s) : 0<returnConstant s := by
  have h := nu_mono (by omega : 1≤1) hs
  rw [nu_one] at h
  unfold returnConstant
  nlinarith [sq_nonneg ((s:ℝ)^2+2+∑ l ∈ Finset.range s, nu (l+1))]

theorem return_loss_envelope {r s : Nat} (hrs : r≤s) (j : Fin r) (e : ℝ) (he : 0≤e)
    (D : Fin r → ℝ) (hD0 : ∀ l, 0≤D l) (hD : ∀ l, D l≤nu (l.val+1)*e) (tau : ℝ)
    (ht0 : 0≤tau) (ht : tau≤((r:ℝ)^2+2)*e) :
    (D j^2+(tau+∑ l, D l)^2)/4≤returnConstant s*e^2 := by
  have hs : 1≤s := by have hj:=j.isLt; omega
  have hnu : 0≤nu s := nu_nonneg hs
  have hd : D j≤nu s*e :=
    (hD j).trans (mul_le_mul_of_nonneg_right (nu_mono (by omega) (by have hj:=j.isLt; omega)) he)
  have hd2 : D j^2≤(nu s*e)^2 := pow_le_pow_left₀ (hD0 j) hd 2
  have hsum : (∑ l, D l)≤(∑ l ∈ Finset.range r, nu (l+1))*e := by
    calc
      _≤∑ l : Fin r, nu (l.val+1)*e := Finset.sum_le_sum (fun l _ => hD l)
      _=_ := by
        rw [← Finset.sum_mul]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun l : Nat => nu (l+1)) r
  have hr2 : (r:ℝ)^2≤(s:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hrs 2
  have htotal : tau+∑ l, D l≤((s:ℝ)^2+2+∑ l ∈ Finset.range s, nu (l+1))*e := by
    have hm := mul_le_mul_of_nonneg_right (sum_nu_mono hrs) he
    have hm2 := mul_le_mul_of_nonneg_right hr2 he
    nlinarith
  have ht2 := pow_le_pow_left₀ (add_nonneg ht0 (Finset.sum_nonneg (fun l _ => hD0 l))) htotal 2
  unfold returnConstant
  nlinarith

end
end Companion.Analytic.ReturnProof
