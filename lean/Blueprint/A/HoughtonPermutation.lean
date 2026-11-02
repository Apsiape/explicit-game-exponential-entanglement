import Blueprint.A.HoughtonTail
import Blueprint.A.HoughtonNormalForm

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem johnsonAlpha_swap : johnsonFiniteHom johnsonAlpha=
    Equiv.swap (Concrete.Ray.one,0) (Concrete.Ray.one,1) := by
  rw [johnsonAlpha_perm]
  apply Equiv.ext
  rintro ⟨r,h⟩
  cases r <;> rcases h with _|_|h
  all_goals simp [Concrete.pPoint,Concrete.qPoint,Concrete.pForward,Concrete.pBackward,
    Concrete.qForward,Concrete.qBackward,Equiv.Perm.mul_apply,Equiv.swap_apply_def]

theorem pPoint_pow_one (j h : Nat) :
    (Concrete.pPoint^j) (Concrete.Ray.one,h)=(Concrete.Ray.one,h+j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih]
    rfl

theorem sigmaZ_perm (j : Nat) : johnsonFiniteHom (sigmaZ j)=
    Equiv.swap (Concrete.Ray.one,j) (Concrete.Ray.one,j+1) := by
  simp only [sigmaZ,map_mul,map_inv,map_zpow,map_pow,johnsonP_perm,johnsonAlpha_swap,zpow_natCast]
  have hc : Concrete.pPoint^j*Equiv.swap (Concrete.Ray.one,0) (Concrete.Ray.one,1)*(Concrete.pPoint^j)⁻¹=
      Equiv.swap ((Concrete.pPoint^j) (Concrete.Ray.one,0)) ((Concrete.pPoint^j) (Concrete.Ray.one,1)) :=
    Equiv.symm_trans_swap_trans _ _ (Concrete.pPoint^j)
  simpa only [pPoint_pow_one,zero_add,Nat.add_comm] using hc

theorem sigmaZ_fixes_high (i j : Nat) (hij : i+1<j) :
    johnsonFiniteHom (sigmaZ i) (Concrete.Ray.one,j)=(Concrete.Ray.one,j) := by
  rw [sigmaZ_perm]
  apply Equiv.swap_apply_of_ne_of_ne <;> intro he <;> have hh := congrArg Prod.snd he <;> omega

theorem coxCoset_preimage (K : Nat) : ∀ k, k≤K →
    johnsonFiniteHom (coxCoset K k) (Concrete.Ray.one,k)=(Concrete.Ray.one,K) := by
  induction K with
  | zero =>
    intro k hk
    have he : k=0 := by omega
    subst k
    simp [coxCoset_self]
  | succ K ih =>
    intro k hk
    by_cases he : k=K+1
    · subst k; simp [coxCoset_self]
    · rw [coxCoset_top K k (by omega),map_mul,Equiv.Perm.mul_apply,ih k (by omega),sigmaZ_perm]
      simp

theorem coxCoset_fixes_high (K : Nat) : ∀ k j, k≤K → K<j →
    johnsonFiniteHom (coxCoset K k) (Concrete.Ray.one,j)=(Concrete.Ray.one,j) := by
  induction K with
  | zero =>
    intro k j hk hj
    have he : k=0 := by omega
    subst k
    simp [coxCoset_self]
  | succ K ih =>
    intro k j hk hj
    by_cases he : k=K+1
    · subst k; simp [coxCoset_self]
    · rw [coxCoset_top K k (by omega),map_mul,Equiv.Perm.mul_apply,ih k j (by omega) (by omega)]
      exact sigmaZ_fixes_high K j hj

theorem coxNormal_fixes_high (K : Nat) (c : Nat → Nat) (hc : CoxNormal K c) (j : Nat) (hj : K<j) :
    johnsonFiniteHom (coxNormalValue K c) (Concrete.Ray.one,j)=(Concrete.Ray.one,j) := by
  induction K with
  | zero => simp [coxNormalValue]
  | succ K ih =>
    rw [coxNormalValue,map_mul,Equiv.Perm.mul_apply,coxCoset_fixes_high (K+1) (c K) j (hc K (by omega)) hj]
    exact ih (fun i hi => hc i (by omega)) (by omega)

/-- A normal form trivial in the concrete adjacent-transposition action is
already the empty free word. This is the missing faithfulness step of collection. -/
theorem coxNormal_null (K : Nat) (c : Nat → Nat) (hc : CoxNormal K c)
    (hnull : johnsonFiniteHom (coxNormalValue K c)=1) : coxNormalValue K c=1 := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hk : c K≤K+1 := hc K (by omega)
    have hcK : CoxNormal K c := fun i hi => hc i (by omega)
    have he := congrArg (fun f : Equiv.Perm Concrete.Point => f (Concrete.Ray.one,c K)) hnull
    rw [coxNormalValue,map_mul,Equiv.Perm.mul_apply,coxCoset_preimage (K+1) (c K) hk,
      coxNormal_fixes_high K c hcK (K+1) (by omega)] at he
    have hlast : c K=K+1 := (congrArg Prod.snd he).symm
    simp only [coxNormalValue,hlast,coxCoset_self,mul_one] at hnull ⊢
    exact ih hcK hnull

theorem johnson_relators_sound (i : Fin 5) : johnsonFiniteHom (johnsonFiniteRelator i)=1 := by
  fin_cases i
  all_goals
    apply Equiv.ext
    rintro ⟨r,h⟩
    cases r <;> rcases h with _|_|_|_|h
    all_goals rfl

theorem johnson_area_sound {w : FreeGroup (Fin 3)} {k : Nat}
    (h : FiniteArea.Area johnsonFiniteRelator w k) : johnsonFiniteHom w=1 := by
  obtain ⟨fs,hfs,he⟩ := h
  rw [←he,map_list_prod]
  have hf (f : FiniteArea.Factor (Fin 3) (Fin 5)) :
      johnsonFiniteHom (FiniteArea.factorValue johnsonFiniteRelator f)=1 := by
    rcases f with ⟨g,i,b⟩
    cases b <;> simp [FiniteArea.factorValue,johnson_relators_sound]
  simp only [List.map_map,Function.comp_def,hf,List.map_const',List.prod_replicate,one_pow]

theorem johnson_close_sound {u v : FreeGroup (Fin 3)} {k : Nat}
    (h : Close johnsonFiniteRelator u v k) : johnsonFiniteHom u=johnsonFiniteHom v := by
  have hh := johnson_area_sound h
  rw [map_mul,map_inv,mul_inv_eq_one] at hh
  exact hh

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.johnsonAlpha_swap
#print axioms Blueprint.HoughtonProof.pPoint_pow_one
#print axioms Blueprint.HoughtonProof.sigmaZ_perm
#print axioms Blueprint.HoughtonProof.sigmaZ_fixes_high
#print axioms Blueprint.HoughtonProof.coxCoset_preimage
#print axioms Blueprint.HoughtonProof.coxCoset_fixes_high
#print axioms Blueprint.HoughtonProof.coxNormal_fixes_high
#print axioms Blueprint.HoughtonProof.coxNormal_null
#print axioms Blueprint.HoughtonProof.johnson_relators_sound
#print axioms Blueprint.HoughtonProof.johnson_area_sound
#print axioms Blueprint.HoughtonProof.johnson_close_sound
