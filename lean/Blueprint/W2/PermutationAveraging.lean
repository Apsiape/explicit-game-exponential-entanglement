import Blueprint.W2.CHSHBookkeeping

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

theorem pair_permutation {α : Type*} [DecidableEq α] (a b c d : α) (hab : a≠b) (hcd : c≠d) :
    ∃ e : Equiv.Perm α, e a=c ∧ e b=d := by
  let t := Equiv.swap a c
  have hta : t a=c := Equiv.swap_apply_left a c
  have htb : t b≠c := by
    intro h
    have hh := t.injective (h.trans hta.symm)
    exact hab hh.symm
  let e := t.trans (Equiv.swap (t b) d)
  refine ⟨e,?_,?_⟩
  · simp only [e,Equiv.trans_apply,hta]
    exact Equiv.swap_apply_of_ne_of_ne htb.symm hcd
  · simp [e]

theorem permutation_pair_sum {n : Nat} (w : Fin n → Fin n → ℝ) (a b c d : Fin n)
    (hab : a≠b) (hcd : c≠d) :
    (∑ p : Equiv.Perm (Fin n), w (p a) (p b))=(∑ p : Equiv.Perm (Fin n), w (p c) (p d)) := by
  obtain ⟨e,ha,hb⟩ := pair_permutation a b c d hab hcd
  have h := Equiv.sum_comp (Equiv.mulRight e) (fun p : Equiv.Perm (Fin n) => w (p a) (p b))
  simpa only [Equiv.coe_mulRight,Equiv.Perm.mul_apply,ha,hb] using h.symm

theorem permutation_ordered_sum {n : Nat} (w : Fin n → Fin n → ℝ) (p : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, ∑ j : Fin n, if i≠j then w (p i) (p j) else 0)=
      ∑ i : Fin n, ∑ j : Fin n, if i≠j then w i j else 0 := by
  have he (i j : Fin n) : i≠j ↔ p i≠p j := p.injective.ne_iff.symm
  have hpoint (i j : Fin n) : (if i≠j then w (p i) (p j) else 0)=
      (if p i≠p j then w (p i) (p j) else 0) := by
    by_cases hij : i=j
    · subst j; simp
    · simp [hij,p.injective.ne hij]
  simp_rw [hpoint]
  have hinner (i : Fin n) :
      (∑ j : Fin n, if p i≠p j then w (p i) (p j) else 0)=
        ∑ j : Fin n, if p i≠j then w (p i) j else 0 :=
    Equiv.sum_comp p (fun j => if p i≠j then w (p i) j else 0)
  simp_rw [hinner]
  exact Equiv.sum_comp p (fun i => ∑ j : Fin n, if i≠j then w i j else 0)

theorem ordered_pair_count (n : Nat) :
    (∑ i : Fin n, ∑ j : Fin n, if i≠j then (1:ℝ) else 0)=(n:ℝ)*(n-1:Nat) := by
  classical
  have hrow (i : Fin n) : (∑ j : Fin n, if i≠j then (1:ℝ) else 0)=(n-1:Nat) := by
    have hf : Finset.univ.filter (fun j : Fin n => i≠j)=Finset.univ.erase i := by
      ext j
      simp [ne_comm]
    rw [Finset.sum_boole,hf]
    simp
  simp_rw [hrow]
  simp

theorem permutation_edges_bound (n : Nat) (hn : 2≤n) (w : Fin n → Fin n → ℝ) (bar : ℝ)
    (hb : (∑ i : Fin n, ∑ j : Fin n, if i≠j then w i j else 0)≤bar*n*(n-1:Nat))
    {ι : Type*} [Fintype ι] (a b : ι → Fin n) (hab : ∀ i, a i≠b i) :
    ∃ p : Equiv.Perm (Fin n), (∑ i, w (p (a i)) (p (b i)))≤bar*Fintype.card ι := by
  let a0 : Fin n := ⟨0,by omega⟩
  let a1 : Fin n := ⟨1,by omega⟩
  let S := ∑ p : Equiv.Perm (Fin n), w (p a0) (p a1)
  let P : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hP : 0<P := by dsimp [P]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card (Equiv.Perm (Fin n)))
  have hPair (i j : Fin n) (hij : i≠j) : (∑ p : Equiv.Perm (Fin n), w (p i) (p j))=S :=
    permutation_pair_sum w i j a0 a1 hij (by intro h; have hh := congrArg Fin.val h; norm_num [a0,a1] at hh)
  have htotal : (n:ℝ)*(n-1:Nat)*S=P*(∑ i : Fin n, ∑ j : Fin n, if i≠j then w i j else 0) := by
    calc
      _=∑ i : Fin n, ∑ j : Fin n, if i≠j then S else 0 := by
        have he (i j : Fin n) : (if i≠j then S else 0)=(if i≠j then (1:ℝ) else 0)*S := by split <;> simp
        simp_rw [he,←Finset.sum_mul,ordered_pair_count]
      _=∑ i : Fin n, ∑ j : Fin n, ∑ p : Equiv.Perm (Fin n), if i≠j then w (p i) (p j) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i=j
        · simp [hij]
        · simpa [hij] using (hPair i j hij).symm
      _=∑ p : Equiv.Perm (Fin n), ∑ i : Fin n, ∑ j : Fin n, if i≠j then w (p i) (p j) else 0 := by
        calc
          _=∑ i : Fin n, ∑ p : Equiv.Perm (Fin n), ∑ j : Fin n, if i≠j then w (p i) (p j) else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
          _=_ := Finset.sum_comm
      _=_ := by simp_rw [permutation_ordered_sum]; simp [P]
  have hS : S≤P*bar := by
    have h := mul_le_mul_of_nonneg_left hb hP.le
    have hN : (0:ℝ)<(n:ℝ)*(n-1:Nat) := by
      have h0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
      have h1 : (0:ℝ)<(n-1:Nat) := by exact_mod_cast (by omega : 0<n-1)
      positivity
    have h' : ((n:ℝ)*(n-1:Nat))*S≤((n:ℝ)*(n-1:Nat))*(P*bar) := by nlinarith only [h,htotal]
    exact (mul_le_mul_iff_right₀ hN).mp h'
  have hsum : (∑ p : Equiv.Perm (Fin n), ∑ i, w (p (a i)) (p (b i)))≤P*(bar*Fintype.card ι) := by
    rw [Finset.sum_comm]
    have he (i : ι) : (∑ p : Equiv.Perm (Fin n), w (p (a i)) (p (b i)))=S := hPair _ _ (hab i)
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg (Fintype.card ι))]
  by_contra! hnone
  have hstrict := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ => hnone p)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hstrict
  change P*(bar*Fintype.card ι)<_ at hstrict
  linarith

theorem permutation_pattern_bound (n : Nat) (hn : 2≤n) (w : Fin n → Fin n → ℝ) (bar : ℝ)
    (hb : (∑ i : Fin n, ∑ j : Fin n, if i≠j then w i j else 0)≤bar*n*(n-1:Nat))
    {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (a b : ι → Fin n) (hab : ∀ i, p i → a i≠b i) :
    ∃ e : Equiv.Perm (Fin n),
      (∑ i, if p i then w (e (a i)) (e (b i)) else 0)≤bar*(∑ i, if p i then (1:ℝ) else 0) := by
  classical
  obtain ⟨e,he⟩ := permutation_edges_bound n hn w bar hb
    (fun i : {i // p i} => a i) (fun i : {i // p i} => b i) (fun i => hab i i.property)
  have hsum (F : ι → ℝ) : (∑ i : {i // p i}, F i)=∑ i, if p i then F i else 0 := by
    rw [←Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) F).symm
  have hc : (Fintype.card {i // p i}:ℝ)=∑ i, if p i then (1:ℝ) else 0 := by
    rw [Finset.sum_boole]
    exact_mod_cast Fintype.card_subtype p
  have he' : (∑ i : {i // p i}, w (e (a i)) (e (b i)))≤bar*Fintype.card {i // p i} := he
  rw [hsum (fun i => w (e (a i)) (e (b i))),hc] at he'
  exact ⟨e,he'⟩

theorem symmetric_ordered_sum (n : Nat) (w : Fin n → Fin n → ℝ) (hsym : ∀ i j, w i j=w j i) :
    (∑ i, ∑ j, if i≠j then w i j else 0)=2*(∑ i, ∑ j, if i<j then w i j else 0) := by
  have he (i j : Fin n) : (if i≠j then w i j else 0)=
      (if i < j then w i j else 0)+(if j < i then w j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · simp
    · simp [h,ne_of_gt h,not_lt_of_ge h.le,hsym]
  simp_rw [he,Finset.sum_add_distrib]
  have hf : (∑ i, ∑ j, if j < i then w j i else 0)=(∑ i, ∑ j, if i < j then w i j else 0) := Finset.sum_comm
  rw [hf]
  ring

theorem symmetric_images_sum {α : Type*} [Fintype α] [DecidableEq α] (n : Nat) (f : α ↪ Fin n)
    (w : Fin n → Fin n → ℝ) (hsym : ∀ i j, w i j=w j i) :
    (∑ i, ∑ j, if i≠j then w (f i) (f j) else 0)=
      2*(∑ i, ∑ j, if f i<f j then w (f i) (f j) else 0) := by
  classical
  have he (i j : α) : (if i≠j then w (f i) (f j) else 0)=
      (if f i<f j then w (f i) (f j) else 0)+(if f j<f i then w (f j) (f i) else 0) := by
    by_cases hij : i=j
    · subst j; simp
    · rcases lt_or_gt_of_ne (f.injective.ne hij) with h | h
      · simp [hij,h,not_lt_of_ge h.le]
      · simp [hij,h,not_lt_of_ge h.le,hsym]
  simp_rw [he,Finset.sum_add_distrib]
  have hf : (∑ i, ∑ j, if f j<f i then w (f j) (f i) else 0)=
      (∑ i, ∑ j, if f i<f j then w (f i) (f j) else 0) := Finset.sum_comm
  rw [hf]
  ring

theorem ordered_sum_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (w : β → β → ℝ) :
    (∑ i : α, ∑ j : α, if i≠j then w (e i) (e j) else 0)=
      ∑ i : β, ∑ j : β, if i≠j then w i j else 0 := by
  classical
  have hpoint (i j : α) : (if i≠j then w (e i) (e j) else 0)=
      (if e i≠e j then w (e i) (e j) else 0) := by
    by_cases hij : i=j
    · subst j; simp
    · simp [hij,e.injective.ne hij]
  simp_rw [hpoint]
  have hinner (i : α) : (∑ j : α, if e i≠e j then w (e i) (e j) else 0)=
      ∑ j : β, if e i≠j then w (e i) j else 0 :=
    Equiv.sum_comp e (fun j => if e i≠j then w (e i) j else 0)
  simp_rw [hinner]
  exact Equiv.sum_comp e (fun i => ∑ j : β, if i≠j then w i j else 0)

end
end Blueprint.W2
