import Blueprint.A.HoughtonCoxeterMoves

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def coxNormalValue : Nat → (Nat → Nat) → FreeGroup (Fin 3)
  | 0,_ => 1
  | K+1,c => coxNormalValue K c*coxCoset (K+1) (c K)

def CoxNormal (K : Nat) (c : Nat → Nat) : Prop := ∀ i<K, c i ≤ i+1

theorem coxNormal_congr (K : Nat) (c d : Nat → Nat) (h : ∀ i<K, c i=d i) :
    coxNormalValue K c=coxNormalValue K d := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [coxNormalValue,ih (fun i hi => h i (by omega)),h K (by omega)]

theorem coxNormal_update (K : Nat) (c : Nat → Nat) (k : Nat) :
    coxNormalValue K (Function.update c K k)=coxNormalValue K c := by
  apply coxNormal_congr
  intro i hi
  exact Function.update_of_ne (by omega : i≠K) k c

theorem coxNormal_extend (K : Nat) (c : Nat → Nat) (k : Nat) :
    coxNormalValue (K+1) (Function.update c K k)=coxNormalValue K c*coxCoset (K+1) k := by
  simp only [coxNormalValue,coxNormal_update,Function.update_self]

theorem coxNormal_wellformed_extend (K : Nat) (c : Nat → Nat) (k : Nat)
    (hc : CoxNormal K c) (hk : k≤K+1) : CoxNormal (K+1) (Function.update c K k) := by
  intro i hi
  by_cases he : i=K
  · subst i
    simpa only [Function.update_self] using hk
  · simpa only [Function.update_of_ne he] using hc i (by omega)

theorem coxCoset_insert (M : Nat) (hM : 2≤M) (K k i : Nat)
    (hk : k≤K) (hi : i<K) (hK : K≤M+1) :
    (∃ k'≤K, Close johnsonFiniteRelator (coxCoset K k*sigmaZ i) (coxCoset K k') 1) ∨
      (∃ j : Nat, j+1<K ∧ Close johnsonFiniteRelator (coxCoset K k*sigmaZ i)
        (sigmaZ j*coxCoset K k) (4*(uniformFarCap M+1)*K)) := by
  by_cases hlo : i+2≤k
  · right
    refine ⟨i,by omega,close_weaken (coxCoset_far_low M hM K k i hk hK hlo) ?_⟩
    have h := Nat.mul_le_mul_right (uniformFarCap M+1) (show K-k≤K by omega)
    nlinarith
  by_cases hext : i+1=k
  · left
    refine ⟨k-1,by omega,?_⟩
    have he : i=k-1 := by omega
    rw [he,coxCoset_extend K k (by omega) hk]
    exact close_weaken (close_refl johnsonFiniteRelator _) (by omega)
  by_cases hcancel : i=k
  · left
    subst i
    exact ⟨k+1,by omega,coxCoset_cancel K k hi⟩
  · right
    refine ⟨i-1,by omega,?_⟩
    exact coxCoset_insert_high M hM K k i (by omega) hi hK

/-- One adjacent transposition is inserted into a finite normal form,
with a quadratic bound in its symmetric-group degree. -/
theorem coxNormal_insert (M : Nat) (hM : 2≤M) (K : Nat) :
    ∀ c : Nat → Nat, CoxNormal K c → K≤M+1 → ∀ i<K,
      ∃ d : Nat → Nat, CoxNormal K d ∧
        Close johnsonFiniteRelator (coxNormalValue K c*sigmaZ i) (coxNormalValue K d)
          (4*(uniformFarCap M+1)*K^2) := by
  induction K with
  | zero => intro c hc hK i hi; omega
  | succ K ih =>
    intro c hc hK i hi
    let k := c K
    have hk : k≤K+1 := hc K (by omega)
    have hcK : CoxNormal K c := fun i hi => hc i (by omega)
    rcases coxCoset_insert M hM (K+1) k i hk hi hK with hplain|hcarry
    · obtain ⟨k',hk',hstep⟩ := hplain
      refine ⟨Function.update c K k',coxNormal_wellformed_extend K c k' hcK hk',?_⟩
      have h := close_left (coxNormalValue K c) hstep
      apply close_weaken (by simpa only [coxNormalValue,coxNormal_update,Function.update_self,mul_assoc,k] using h)
      have hF : 1≤uniformFarCap M+1 := by omega
      nlinarith
    · obtain ⟨j,hj,hstep⟩ := hcarry
      obtain ⟨d,hd,hinsert⟩ := ih c hcK (by omega) j (by omega)
      have h1 := close_left (coxNormalValue K c) hstep
      have h2 := close_right (coxCoset (K+1) k) hinsert
      have h := close_trans h1 (by simpa only [mul_assoc] using h2)
      refine ⟨Function.update d K k,coxNormal_wellformed_extend K d k hd hk,?_⟩
      apply close_weaken (by simpa only [coxNormalValue,coxNormal_update,Function.update_self,mul_assoc,k] using h)
      nlinarith

def positiveSigmaValue (w : List Nat) : FreeGroup (Fin 3) := (w.map (fun i : Nat => sigmaZ (i:ℤ))).prod

theorem coxNormal_collect (M : Nat) (hM : 2≤M) (K : Nat) (hK : K≤M+1)
    (w : List Nat) (hw : ∀ i∈w, i<K) (c : Nat → Nat) (hc : CoxNormal K c) :
    ∃ d : Nat → Nat, CoxNormal K d ∧
      Close johnsonFiniteRelator (coxNormalValue K c*positiveSigmaValue w) (coxNormalValue K d)
        (w.length*(4*(uniformFarCap M+1)*K^2)) := by
  induction w generalizing c with
  | nil => exact ⟨c,hc,by simpa [positiveSigmaValue] using close_refl johnsonFiniteRelator _⟩
  | cons i w ih =>
    obtain ⟨d,hd,hi⟩ := coxNormal_insert M hM K c hc hK i (hw i (by simp))
    obtain ⟨e,he,hw'⟩ := ih (fun j hj => hw j (by simp [hj])) d hd
    have h1 := close_right (positiveSigmaValue w) hi
    have h := close_trans h1 hw'
    refine ⟨e,he,?_⟩
    convert h using 1
    · simp only [positiveSigmaValue,List.map_cons,List.prod_cons,mul_assoc]
    · simp only [List.length_cons]
      ring

theorem coxNormal_empty (K : Nat) : coxNormalValue K (fun i => i+1)=1 := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [coxNormalValue,coxCoset_self,ih,mul_one]

theorem positive_word_normal_form (M : Nat) (hM : 2≤M) (K : Nat) (hK : K≤M+1)
    (w : List Nat) (hw : ∀ i∈w, i<K) :
    ∃ d : Nat → Nat, CoxNormal K d ∧
      Close johnsonFiniteRelator (positiveSigmaValue w) (coxNormalValue K d)
        (w.length*(4*(uniformFarCap M+1)*K^2)) := by
  simpa only [coxNormal_empty,one_mul] using
    coxNormal_collect M hM K hK w hw (fun i => i+1) (fun _ _ => le_rfl)

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.coxNormalValue
#print axioms Blueprint.HoughtonProof.CoxNormal
#print axioms Blueprint.HoughtonProof.coxNormal_congr
#print axioms Blueprint.HoughtonProof.coxNormal_update
#print axioms Blueprint.HoughtonProof.coxNormal_extend
#print axioms Blueprint.HoughtonProof.coxNormal_wellformed_extend
#print axioms Blueprint.HoughtonProof.coxCoset_insert
#print axioms Blueprint.HoughtonProof.coxNormal_insert
#print axioms Blueprint.HoughtonProof.positiveSigmaValue
#print axioms Blueprint.HoughtonProof.coxNormal_collect
#print axioms Blueprint.HoughtonProof.coxNormal_empty
#print axioms Blueprint.HoughtonProof.positive_word_normal_form
