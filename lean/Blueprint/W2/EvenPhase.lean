import Blueprint.W2.EvenPermutations

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def evenPhase (m j : Nat) : ℂ := Complex.exp ((((Real.pi/(m:ℝ))*j:ℝ):ℂ)*Complex.I)

theorem evenPhase_formula (m : Nat) (hm : 0<m) (j : Nat) :
    evenPhase m j=Complex.exp (((2*Real.pi*j/(2*m):ℝ):ℂ)*Complex.I) := by
  unfold evenPhase
  congr 2
  push_cast
  ring

theorem evenPhase_zero (m : Nat) : evenPhase m 0=1 := by simp [evenPhase]

theorem evenPhase_add (m i j : Nat) : evenPhase m (i+j)=evenPhase m i*evenPhase m j := by
  unfold evenPhase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem evenPhase_half (m : Nat) (hm : 0<m) : evenPhase m m=-1 := by
  rw [evenPhase]
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast (ne_of_gt hm)
  rw [div_mul_cancel₀ _ hm0]
  exact Complex.exp_pi_mul_I

theorem evenPhase_period (m : Nat) (hm : 0<m) : evenPhase m (2*m)=1 := by
  rw [show 2*m=m+m from by omega,evenPhase_add,evenPhase_half m hm]
  norm_num

theorem evenPhase_mod (m : Nat) (hm : 0<m) (j : Nat) : evenPhase m (j%(2*m))=evenPhase m j := by
  have hmultiple (q : Nat) : evenPhase m ((2*m)*q)=1 := by
    induction q with
    | zero => simp [evenPhase_zero]
    | succ q ih => rw [Nat.mul_succ,evenPhase_add,ih,evenPhase_period m hm,one_mul]
  have he := Nat.mod_add_div j (2*m)
  have hh := congrArg (evenPhase m) he
  rw [evenPhase_add,hmultiple,mul_one] at hh
  exact hh

theorem evenPhase_unit (m j : Nat) :
    star (evenPhase m j)*evenPhase m j=1 ∧ evenPhase m j*star (evenPhase m j)=1 := by
  have hn : ‖evenPhase m j‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hh : Complex.normSq (evenPhase m j)=1 := by rw [Complex.normSq_eq_norm_sq,hn,one_pow]
  constructor
  · rw [mul_comm,Complex.star_def,Complex.mul_conj,hh]; rfl
  · rw [Complex.star_def,Complex.mul_conj,hh]; rfl

theorem evenPhase_shift (m : Nat) (hm : 0<m) (i : Fin (2*m)) :
    evenPhase m (halfSwap m hm i).val= -evenPhase m i.val := by
  rw [halfSwap_val,evenPhase_mod m hm,evenPhase_add,evenPhase_half m hm]
  ring

theorem evenPhase_double (m j : Nat) : evenPhase m (2*j)=evenPhase m j*evenPhase m j := by
  rw [show 2*j=j+j from by omega,evenPhase_add]

theorem evenPhase_shuffle (m : Nat) (hm : 0<m) (i : Fin (2*m)) :
    evenPhase m (shuffle m hm i).val=evenPhase m i.val*evenPhase m i.val*
      (if i.val<m then 1 else evenPhase m 1) := by
  change evenPhase m (if i.val<m then 2*i.val else 2*(i.val-m)+1)=_
  by_cases hi : i.val<m
  · simp only [hi,↓reduceIte,mul_one,evenPhase_double]
  · have he : evenPhase m (i.val-m)= -evenPhase m i.val := by
      have hnat : i.val-m+m=i.val := by omega
      have hp := evenPhase_add m (i.val-m) m
      rw [hnat,evenPhase_half m hm] at hp
      rw [hp]
      ring
    simp only [hi,↓reduceIte,evenPhase_add,evenPhase_double,he]
    ring

end
end Blueprint.W2
