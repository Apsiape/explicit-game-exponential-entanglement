import Blueprint.W2.CHSHExact

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem modulo_partner_count (n k : Nat) (hk : 0<k) (i : Fin n) :
    ((Finset.univ.filter (fun j : Fin n => i≠j ∧ i.val%k=j.val%k)).card)≤n/k := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => i≠j ∧ i.val%k=j.val%k)
  let T := (Finset.range (n/k+1)).erase (i.val/k)
  have hi : i.val/k<n/k+1 := Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)
  have hm (j : Fin n) (hj : j∈S) : j.val/k∈T := by
    obtain ⟨hne,hmod⟩ := (Finset.mem_filter.mp hj).2
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right j.isLt.le))⟩
    intro he
    have hval : i.val=j.val := by
      have hi' := Nat.mod_add_div i.val k
      have hj' := Nat.mod_add_div j.val k
      rw [hmod,←he] at hi'
      exact hi'.symm.trans hj'
    exact hne (Fin.ext hval)
  have hinj : Set.InjOn (fun j : Fin n => j.val/k) S := by
    intro j hj l hl he
    have hmj := (Finset.mem_filter.mp hj).2.2
    have hml := (Finset.mem_filter.mp hl).2.2
    apply Fin.ext
    have hj' := Nat.mod_add_div j.val k
    have hl' := Nat.mod_add_div l.val k
    change j.val/k=l.val/k at he
    rw [hmj.symm.trans hml,he] at hj'
    exact hj'.symm.trans hl'
  have hc := Finset.card_le_card_of_injOn (f:=fun j : Fin n => j.val/k) hm hinj
  have hT : T.card=n/k := by simp [T,Finset.card_erase_of_mem (Finset.mem_range.mpr hi)]
  rw [hT] at hc
  exact hc

theorem modulo_collision_budget (n k : Nat) (hk : 0<k) :
    (∑ i : Fin n, ∑ j : Fin n, if i<j ∧ i.val%k=j.val%k then (1:ℝ) else 0)≤
      (n:ℝ)*(n/k:Nat) := by
  have hrow (i : Fin n) :
      (∑ j : Fin n, if i<j ∧ i.val%k=j.val%k then (1:ℝ) else 0)≤(n/k:Nat) := by
    have hsub :
        Finset.univ.filter (fun j : Fin n => i<j ∧ i.val%k=j.val%k)⊆
          Finset.univ.filter (fun j : Fin n => i≠j ∧ i.val%k=j.val%k) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨ne_of_lt (Finset.mem_filter.mp hj).2.1,(Finset.mem_filter.mp hj).2.2⟩⟩
    have hc := (Finset.card_le_card hsub).trans (modulo_partner_count n k hk i)
    simpa only [←Finset.sum_boole] using (show
      ((Finset.univ.filter (fun j : Fin n => i<j ∧ i.val%k=j.val%k)).card:ℝ)≤(n/k:Nat) by exact_mod_cast hc)
  calc
    _≤∑ _ : Fin n, ((n/k:Nat):ℝ) := Finset.sum_le_sum (fun i _ => hrow i)
    _=_ := by simp

def collisionBob {n k d : Nat} (G : Fin k → Mat d) (f : Fin n → Fin k) (i j : Fin n) : Mat d :=
  if f i=f j then (G (f i)).transpose else exactBob (fun i => G (f i)) i j

theorem collisionBob_involution {n k d : Nat} (G : Fin k → Mat d) (f : Fin n → Fin k)
    (hG : ∀ i, IsInvolution (G i)) (ha : ∀ i j, i≠j → anti (G i) (G j)=0)
    (i j : Fin n) : IsInvolution (collisionBob G f i j) := by
  unfold collisionBob
  split
  · exact ReturnProof.transpose_involution _ (hG _)
  · unfold exactBob
    split
    · exact ReturnProof.transpose_involution _ (chshPlus_involution _ _ (hG _) (hG _) (ha _ _ ‹_›))
    · split
      · exact ReturnProof.transpose_involution _ (chshMinus_involution _ _ (hG _) (hG _) (ha _ _ (Ne.symm ‹_›)))
      · simp [IsInvolution]

theorem collision_pair_lower {n k d : Nat} (hd : 0<d) (G : Fin k → Mat d) (f : Fin n → Fin k)
    (hG : ∀ i, IsInvolution (G i)) (i j : Fin n) (hij : i<j) :
    2*Real.sqrt 2-Real.sqrt 2*(if f i=f j then 1 else 0)≤
      chshPair (MainProof.flatState d hd).xi (fun i => G (f i)) (collisionBob G f) i j := by
  by_cases hf : f i=f j
  · have hp : collisionBob G f i j+collisionBob G f j i=(2:ℂ) • (G (f i)).transpose := by
      simp only [collisionBob,hf,↓reduceIte]
      module
    have hm : collisionBob G f i j-collisionBob G f j i=0 := by simp [collisionBob,hf]
    simp only [hf,↓reduceIte,mul_one,chshPair,hp,hm]
    have he := flat_expectation_real hd (G (f j)) (hG (f j)) 2
    norm_num only [Complex.ofReal_ofNat] at he
    rw [he]
    have hz : expectation (MainProof.flatState d hd).xi (G (f j)) 0=0 := by
      simp [expectation,Matrix.zero_mul,Matrix.zero_apply]
    rw [hz]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  · have hp := exactBob_pair (fun i => G (f i)) i j hij
    have hb (p q : Fin n) (h : f p≠f q) :
        collisionBob G f p q=exactBob (fun i => G (f i)) p q := by simp [collisionBob,h]
    simp only [hf,↓reduceIte,mul_zero,sub_zero,chshPair,hb i j hf,hb j i (Ne.symm hf)]
    rw [hp.1,hp.2,flat_expectation hd _ (hG _),flat_expectation hd _ (hG _)]
    linarith

theorem collision_bias {n k d : Nat} (hn : 2≤n) (hk : 0<k) (hd : 0<d)
    (G : Fin k → Mat d) (hG : ∀ i, IsInvolution (G i)) (eps : ℝ)
    (hbudget : ((n/k:Nat):ℝ)≤eps*(n-1:Nat)) :
    let f : Fin n → Fin k := fun i => ⟨i.val%k,Nat.mod_lt _ hk⟩
    (1-eps)*optimalBias≤chshBias (MainProof.flatState d hd).xi
      (fun i => G (f i)) (collisionBob G f) := by
  dsimp only
  let f : Fin n → Fin k := fun i => ⟨i.val%k,Nat.mod_lt _ hk⟩
  let C := chshPair (MainProof.flatState d hd).xi (fun i => G (f i)) (collisionBob G f)
  let T := ∑ i : Fin n, ∑ j : Fin n, if i<j ∧ i.val%k=j.val%k then (1:ℝ) else 0
  have ht : T≤(n:ℝ)*(n/k:Nat) := modulo_collision_budget n k hk
  have hsum : (2*Real.sqrt 2)*(n.choose 2)-Real.sqrt 2*T≤
      ∑ i : Fin n, ∑ j : Fin n, if i<j then C i j else 0 := by
    have hp (i j : Fin n) :
        (2*Real.sqrt 2)*(if i<j then 1 else 0)-
          Real.sqrt 2*(if i<j ∧ i.val%k=j.val%k then 1 else 0)≤
            (if i<j then C i j else 0) := by
      by_cases hij : i<j
      · have hh := collision_pair_lower hd G f hG i j hij
        have hf : f i=f j ↔ i.val%k=j.val%k := Fin.ext_iff
        simpa only [hij,true_and,↓reduceIte,mul_one,hf,C] using hh
      · simp [hij]
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hp i j))
    simp only [Finset.sum_sub_distrib,←Finset.mul_sum,W2.pair_count] at h
    exact h
  have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hnP : (0:ℝ)<(n-1:Nat) := by exact_mod_cast (by omega : 0<n-1)
  have hbound : T≤(n:ℝ)*(eps*(n-1:Nat)) :=
    ht.trans (mul_le_mul_of_nonneg_left hbudget hnR.le)
  rw [W2.choose_two_cast] at hsum
  unfold chshBias optimalBias
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*n*(n-1:Nat))).mpr
  change _≤∑ i : Fin n, ∑ j : Fin n, if i<j then C i j else 0
  nlinarith [mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg (2:ℝ))]

theorem ceiling_collision_budget (n : Nat) (hn : 2≤n) (eps : ℝ) (he : 0<eps) :
    ((n/(2*⌈1/eps⌉₊+1):Nat):ℝ)≤eps*(n-1:Nat) := by
  let m := ⌈1/eps⌉₊
  have hmR : (0:ℝ)<m := (by positivity : (0:ℝ)<1/eps).trans_le (Nat.le_ceil _)
  have hm : 0<m := by exact_mod_cast hmR
  have hM : (1:ℝ)/m≤eps := by
    have hh := Nat.le_ceil (1/eps:ℝ)
    change (1:ℝ)/eps≤m at hh
    exact (div_le_iff₀ hmR).mpr (by nlinarith [(div_le_iff₀ he).mp hh])
  have hq : (n/(2*m+1))*m≤n-1 := by
    have hdiv := Nat.div_mul_le_self n (2*m+1)
    have hn2 : n≤2*(n-1) := by omega
    nlinarith
  have hqR : ((n/(2*m+1):Nat):ℝ)≤((n-1:Nat):ℝ)/m := by
    apply (le_div_iff₀ hmR).mpr
    exact_mod_cast hq
  exact hqR.trans (by simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg (n-1)))

end
end Blueprint.W2
