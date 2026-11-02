import Blueprint.A.HashNullBounds

namespace Blueprint.AHash
noncomputable section
open Companion Concrete Companion.Analytic
open scoped Classical BigOperators
set_option maxHeartbeats 600000

theorem finite_bad_rows {α : Type} [Fintype α] [DecidableEq α] (U : Matrix α α ℂ)
    (hU : U.conjTranspose*U=1 ∧ U*U.conjTranspose=1) (G : Finset α)
    (hG : ∀ i∈G, ∀ j, U i j=(1:Matrix α α ℂ) i j) :
    hsNorm (U-1)^2≤4*((Fintype.card α:ℝ)-G.card) := by
  have hUd : U.conjTranspose.conjTranspose*U.conjTranspose=1 ∧
      U.conjTranspose*U.conjTranspose.conjTranspose=1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
  have hGd : ∀ j∈G, ∀ i, U.conjTranspose i j=(1:Matrix α α ℂ) i j := by
    intro j hj i
    change star (U j i)=(1:Matrix α α ℂ) i j
    rw [hG j hj i]
    simp [Matrix.one_apply,eq_comm]
  have hh := finite_bad_columns U.conjTranspose hUd G hGd
  have he : U.conjTranspose-1=(U-1).conjTranspose := by
    ext i j
    simp [Matrix.conjTranspose_apply,Matrix.one_apply,eq_comm]
  rw [he,hsNorm_conjTranspose] at hh
  exact hh

def clockBadHash (m k : Nat) (w : List Letter) (c : FiniteClock m) : Finset (ClockHash m k) :=
  Finset.univ.filter (fun eta => ¬Set.InjOn (hashApply eta) (hashProductSites (clockWordGammas m w c) : Set _))

def clockRowEmbed (m k : Nat) (c : FiniteClock m) : ClockFibre m k ↪ ClockModelIndex m k where
  toFun v := (c,v)
  inj' := fun _ _ h => congrArg Prod.snd h

def clockGoodRows (m k ell : Nat) (hl : ell≤m) (w : List Letter) : Finset (ClockModelIndex m k) :=
  (clockInterior m ell hl).biUnion (fun c =>
    (Finset.product (clockBadHash m k w c)ᶜ (Finset.univ : Finset (ClockRegister k))).map (clockRowEmbed m k c))

theorem clockGoodRows_card (m k ell : Nat) (hl : ell≤m) (w : List Letter) :
    (clockGoodRows m k ell hl w).card=
      ∑ c∈clockInterior m ell hl, ((Fintype.card (ClockHash m k)-(clockBadHash m k w c).card)*
        Fintype.card (ClockRegister k)) := by
  unfold clockGoodRows
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.card_map]
    simpa only [Finset.product_eq_sprod,Finset.card_compl,Finset.card_univ] using
      (Finset.card_product ((clockBadHash m k w c)ᶜ) (Finset.univ : Finset (ClockRegister k)))
  · intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨v,_,hv⟩ := Finset.mem_map.mp hi
    obtain ⟨u,_,hu⟩ := Finset.mem_map.mp hj
    exact hcd (congrArg Prod.fst (hv.trans hu.symm))

theorem clockGoodRows_correct (m k ell : Nat) (hl : ell≤m) (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell) :
    ∀ i∈clockGoodRows m k ell hl (w.map hashDecode), ∀ j,
      (clockModelHom m k (FreeGroup.mk w):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ) i j=
        (1:Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ) i j := by
  intro i hi j
  obtain ⟨c,hc,hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨⟨eta,v⟩,hv,rfl⟩ := Finset.mem_map.mp hi
  have hgood : Set.InjOn (hashApply eta) (hashProductSites (clockWordGammas m (w.map hashDecode) c) : Set _) := by
    have hh := (Finset.mem_product.mp hv).1
    simpa only [Finset.mem_compl,clockBadHash,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hh
  exact clockModelHom_null_row m k ell hl w hw hL c hc eta hgood v j

theorem clockBadHash_bound (m k ell : Nat) (w : List Letter) (hL : w.length≤ell) (c : FiniteClock m) :
    ((clockBadHash m k w c).card:ℝ)≤(ell.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ))*Fintype.card (ClockHash m k) := by
  have hp : (0:ℝ)<Fintype.card (ClockHash m k) := by exact_mod_cast Fintype.card_pos
  have hh := (div_le_iff₀ hp).mp (affine_collision (3*(2*m+3)) k (hashProductSites (clockWordGammas m w c)))
  apply hh.trans
  have hs := (clockWordGammas_sites_card m w c).trans hL
  have hchoose : ((hashProductSites (clockWordGammas m w c)).card.choose 2:ℝ)≤(ell.choose 2:ℝ) :=
    by exact_mod_cast Nat.choose_le_choose 2 hs
  gcongr

theorem clockGoodRows_lower (m k ell : Nat) (hl : ell≤m) (w : List Letter) (hL : w.length≤ell) :
    ((clockInterior m ell hl).card:ℝ)*(1-(ell.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ)))*Fintype.card (ClockFibre m k)≤
      (clockGoodRows m k ell hl w).card := by
  rw [clockGoodRows_card]
  push_cast
  simp only [Nat.cast_sub (Finset.card_le_univ _)]
  have he : ((clockInterior m ell hl).card:ℝ)*(1-(ell.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ)))*Fintype.card (ClockFibre m k)=
      ∑ c∈clockInterior m ell hl,
        ((1-(ell.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ)))*Fintype.card (ClockHash m k))*Fintype.card (ClockRegister k) := by
    simp only [Finset.sum_const,nsmul_eq_mul,ClockFibre,Fintype.card_prod,Nat.cast_mul]
    ring
  rw [he]
  apply Finset.sum_le_sum
  intro c hc
  have hh := clockBadHash_bound m k ell w hL c
  have hf : (0:ℝ)≤Fintype.card (ClockRegister k) := Nat.cast_nonneg _
  nlinarith

theorem clockModelHom_null_defect (m k ell : Nat) (hm : 1≤m) (hl : ell≤m) (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell) :
    hsNorm ((clockModelHom m k (FreeGroup.mk w):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)-1)^2≤
      4*(4*(ell:ℝ)/(2*m+1)+(ell.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ)))*clockModelDimension m k := by
  let U := (clockModelHom m k (FreeGroup.mk w):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)
  have hu := (clockModelHom m k (FreeGroup.mk w)).property
  have hh := finite_bad_rows U hu (clockGoodRows m k ell hl (w.map hashDecode))
    (clockGoodRows_correct m k ell hl w hw hL)
  have hgood := clockGoodRows_lower m k ell hl (w.map hashDecode) (by simpa only [List.length_map] using hL)
  have hi : ((clockInterior m ell hl).card:ℝ)≤Fintype.card (FiniteClock m) := by exact_mod_cast Finset.card_le_univ _
  have hC : (0:ℝ)<Fintype.card (FiniteClock m) := by exact_mod_cast Fintype.card_pos
  have hF : (0:ℝ)<Fintype.card (ClockFibre m k) := by exact_mod_cast Fintype.card_pos
  have hb : (0:ℝ)≤(ell.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ)) := by positivity
  have hboundary := clockInterior_boundary m ell hm hl
  have hboundary' : (Fintype.card (FiniteClock m):ℝ)-(clockInterior m ell hl).card≤
      (4*(ell:ℝ)/(2*m+1))*Fintype.card (FiniteClock m) := by
    have he : ((Fintype.card (FiniteClock m):ℝ)-(clockInterior m ell hl).card)/
        Fintype.card (FiniteClock m)≤4*(ell:ℝ)/(2*m+1) := by
      rw [sub_div,div_self (ne_of_gt hC)]
      exact hboundary
    exact (div_le_iff₀ hC).mp he
  have hd : (clockModelDimension m k:ℝ)=(Fintype.card (FiniteClock m):ℝ)*Fintype.card (ClockFibre m k) := by
    simp only [clockModelDimension,ClockModelIndex,Fintype.card_prod,Nat.cast_mul]
  rw [hd]
  change hsNorm (U-1)^2≤_
  change hsNorm (U-1)^2≤4*((Fintype.card (ClockModelIndex m k):ℝ)-(clockGoodRows m k ell hl (w.map hashDecode)).card) at hh
  have hdim : (Fintype.card (ClockModelIndex m k):ℝ)=
      (Fintype.card (FiniteClock m):ℝ)*Fintype.card (ClockFibre m k) := hd
  rw [hdim] at hh
  nlinarith [mul_le_mul_of_nonneg_right hi hb,
    mul_le_mul_of_nonneg_right hboundary' (le_of_lt hF),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hb) (le_of_lt hF)]

end
end Blueprint.AHash

#print axioms Blueprint.AHash.finite_bad_rows
#print axioms Blueprint.AHash.clockBadHash
#print axioms Blueprint.AHash.clockRowEmbed
#print axioms Blueprint.AHash.clockGoodRows
#print axioms Blueprint.AHash.clockGoodRows_card
#print axioms Blueprint.AHash.clockGoodRows_correct
#print axioms Blueprint.AHash.clockBadHash_bound
#print axioms Blueprint.AHash.clockGoodRows_lower
#print axioms Blueprint.AHash.clockModelHom_null_defect
