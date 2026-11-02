import Blueprint.W2.PermutationAveraging

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

theorem select_triples (n M : Nat) (hM : 1≤M) (hn : 3*M≤n)
    (delta : Fin n → Fin n → ℝ) (hsym : ∀ i j, delta i j=delta j i) (bar : ℝ)
    (hb : (∑ i, ∑ j, if i<j then delta i j else 0)≤bar*(n.choose 2)) :
    ∃ f : (Fin M × Fin 3) ↪ Fin n,
      (∑ x, ∑ y, if f x<f y then delta (f x) (f y) else 0)≤bar*((3*M).choose 2) ∧
      (∑ k, ∑ r : Fin 3, ∑ s : Fin 3, if r<s then delta (f (k,r)) (f (k,s)) else 0)≤bar*(3*M:Nat) := by
  classical
  let k := 3*M
  have hk : 2≤k := by dsimp [k]; omega
  have hn2 : 2≤n := by omega
  let q : Fin k ↪ Fin n := Fin.castLEEmb hn
  have hbudget : (∑ i, ∑ j, if i≠j then delta i j else 0)≤bar*n*(n-1:Nat) := by
    rw [symmetric_ordered_sum n delta hsym]
    rw [choose_two_cast] at hb
    nlinarith only [hb]
  obtain ⟨sigma,hsigma⟩ := permutation_pattern_bound n hn2 delta bar hbudget
    (fun z : Fin k × Fin k => z.1≠z.2) (fun z => q z.1) (fun z => q z.2)
    (fun z hz => q.injective.ne hz)
  let F : Fin k ↪ Fin n := q.trans sigma.toEmbedding
  let w : Fin k → Fin k → ℝ := fun i j => delta (F i) (F j)
  have hw : (∑ i, ∑ j, if i≠j then w i j else 0)≤bar*k*(k-1:Nat) := by
    simpa only [Fintype.sum_prod_type,ordered_pair_count,F,Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply,w,mul_assoc] using hsigma
  let e : Fin M × Fin 3 ≃ Fin k := finProdFinEquiv.trans (finCongr (Nat.mul_comm M 3))
  obtain ⟨tau,htau⟩ := permutation_pattern_bound k hk w bar hw
    (fun z : Fin M × (Fin 3 × Fin 3) => z.2.1≠z.2.2)
    (fun z => e (z.1,z.2.1)) (fun z => e (z.1,z.2.2))
    (fun z hz => e.injective.ne (fun hh => hz (congrArg Prod.snd hh)))
  let f : (Fin M × Fin 3) ↪ Fin n := (e.toEmbedding.trans tau.toEmbedding).trans F
  have hInternal :
      (∑ t : Fin M, ∑ r : Fin 3, ∑ s : Fin 3,
        if r≠s then delta (f (t,r)) (f (t,s)) else 0)≤bar*(6*M:Nat) := by
    have hcount : (∑ z : Fin M × (Fin 3 × Fin 3), if z.2.1≠z.2.2 then (1:ℝ) else 0)=(6*M:Nat) := by
      simp only [Fintype.sum_prod_type,ordered_pair_count]
      norm_num
      ring
    rw [hcount] at htau
    simpa only [Fintype.sum_prod_type,f,F,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,w] using htau
  have hTotal :
      (∑ x : Fin M × Fin 3, ∑ y : Fin M × Fin 3, if x≠y then delta (f x) (f y) else 0)≤
        bar*k*(k-1:Nat) := by
    have he := ordered_sum_equiv e (fun i j => w (tau i) (tau j))
    rw [permutation_ordered_sum w tau] at he
    have hh : (∑ x : Fin M × Fin 3, ∑ y : Fin M × Fin 3, if x≠y then delta (f x) (f y) else 0)=
        (∑ i, ∑ j, if i≠j then w i j else 0) := by
      simpa only [f,F,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,w] using he
    rw [hh]
    exact hw
  refine ⟨f,?_,?_⟩
  · rw [symmetric_images_sum n f delta hsym] at hTotal
    rw [choose_two_cast]
    change _≤bar*((k:ℝ)*(k-1:Nat)/2)
    linarith only [hTotal]
  · have heach (t : Fin M) := symmetric_ordered_sum 3
      (fun r s => delta (f (t,r)) (f (t,s))) (fun r s => hsym _ _)
    simp_rw [heach,←Finset.mul_sum] at hInternal
    push_cast at hInternal ⊢
    nlinarith only [hInternal]

end
end Blueprint.W2
