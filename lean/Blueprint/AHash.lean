import Blueprint.AGadget
import Blueprint.AWordArea
import Blueprint.A.HashAlphabet
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

namespace Blueprint.AHash
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def hashApply {n k : Nat} (h : (Fin k → Fin n → Bool) × (Fin k → Bool))
    (x : Fin n → Bool) (j : Fin k) : Bool :=
  (List.ofFn (fun i => h.1 j i && x i)).foldl Bool.xor (h.2 j)

theorem xor_fold_sum (l : List Bool) (b : Bool) : l.foldl Bool.xor b=b+l.sum := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simpa only [List.foldl_cons,ih,List.sum_cons,Bool.add_eq_xor] using Bool.xor_assoc b a l.sum

theorem hash_linear {n k : Nat} (h : (Fin k → Fin n → Bool) × (Fin k → Bool))
    (x : Fin n → Bool) (j : Fin k) : hashApply h x j=h.2 j+∑ i, h.1 j i*x i := by
  rw [hashApply,xor_fold_sum,List.sum_ofFn]
  rfl

def collisionHom {n k : Nat} (x y : Fin n → Bool) :
    ((Fin k → Fin n → Bool) × (Fin k → Bool)) →+ (Fin k → Bool) where
  toFun h j := ∑ i, h.1 j i*(x i+y i)
  map_zero' := by ext j; simp
  map_add' h g := by ext j; simp [add_mul,Finset.sum_add_distrib]

theorem hash_collision_iff {n k : Nat} (x y : Fin n → Bool)
    (h : (Fin k → Fin n → Bool) × (Fin k → Bool)) :
    hashApply h x=hashApply h y ↔ collisionHom (k:=k) x y h=0 := by
  simp only [funext_iff,hash_linear,collisionHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    mul_add,Finset.sum_add_distrib,Pi.zero_apply]
  apply forall_congr'
  intro j
  rw [add_left_cancel_iff,add_eq_zero_iff_eq_neg]
  rfl

theorem collision_surjective {n k : Nat} (x y : Fin n → Bool) (hxy : x≠y) :
    Function.Surjective (collisionHom (k:=k) x y) := by
  classical
  have hi : ∃ i, x i≠y i := by contrapose! hxy; exact funext hxy
  obtain ⟨i,hi⟩ := hi
  have hv : x i+y i=true := by
    cases hx : x i <;> cases hy : y i <;> simp_all [Bool.add_eq_xor]
  intro v
  refine ⟨(fun j l => if l=i then v j else 0,0),?_⟩
  ext j
  change (∑ l, (if l=i then v j else 0)*(x l+y l))=v j
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,hv]
  exact Bool.and_true _

theorem pair_collision_probability {n k : Nat} (x y : Fin n → Bool) (hxy : x≠y) :
    ((Finset.univ.filter (fun h : (Fin k → Fin n → Bool) × (Fin k → Bool) =>
      hashApply h x=hashApply h y)).card:ℝ) /
      Fintype.card ((Fin k → Fin n → Bool) × (Fin k → Bool))=(2:ℝ)^(-(k:ℤ)) := by
  classical
  let f := collisionHom (k:=k) x y
  have hcard : (Finset.univ.filter (fun h : (Fin k → Fin n → Bool) × (Fin k → Bool) =>
      hashApply h x=hashApply h y)).card=Fintype.card f.ker := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext h
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,AddMonoidHom.mem_ker]
    exact hash_collision_iff x y h
  have hc := AddSubgroup.card_ker_mul_card_of_surjective (f:=f) (collision_surjective x y hxy)
  have hcod : Fintype.card (Fin k → Bool)=2^k := by simp
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,
    hcod] at hc
  rw [hcard,zpow_neg,zpow_natCast]
  have hD : (Fintype.card ((Fin k → Fin n → Bool) × (Fin k → Bool)):ℝ)≠0 := by positivity
  have hpow : (2:ℝ)^k≠0 := by positivity
  rw [div_eq_iff hD]
  rw [mul_comm ((2:ℝ)^k)⁻¹,←div_eq_mul_inv]
  apply (eq_div_iff hpow).mpr
  exact_mod_cast hc

theorem affine_collision (n k : Nat) (S : Finset (Fin n → Bool)) :
    ((Finset.univ.filter (fun h : (Fin k → Fin n → Bool) × (Fin k → Bool) =>
      ¬Set.InjOn (hashApply h) (S:Set (Fin n → Bool)))).card:ℝ) /
      Fintype.card ((Fin k → Fin n → Bool) × (Fin k → Bool))≤
        (S.card.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ)) := by
  classical
  let H := (Fin k → Fin n → Bool) × (Fin k → Bool)
  let P := S.powersetCard 2
  let bad := fun p : Finset (Fin n → Bool) =>
    Finset.univ.filter (fun h : H => ¬Set.InjOn (hashApply h) (p:Set (Fin n → Bool)))
  have hcover : bad S⊆P.biUnion bad := by
    intro h hh
    have hn := (Finset.mem_filter.mp hh).2
    simp only [Set.InjOn,Finset.mem_coe] at hn
    push Not at hn
    obtain ⟨x,hx,y,hy,hf,hxy⟩ := hn
    apply Finset.mem_biUnion.mpr
    refine ⟨{x,y},?_,?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_,Finset.card_pair hxy⟩
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl
      · exact hx
      · exact hy
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro hi
      exact hxy (hi (by simp) (by simp) hf)
  have hp (p : Finset (Fin n → Bool)) (hP : p∈P) :
      ((bad p).card:ℝ)/Fintype.card H=(2:ℝ)^(-(k:ℤ)) := by
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2
    have heq : bad {x,y}=Finset.univ.filter (fun h : H => hashApply h x=hashApply h y) := by
      ext h
      simp only [bad,Finset.mem_filter,Finset.mem_univ,true_and,Finset.coe_pair,Set.injOn_pair]
      exact ⟨fun hn => by tauto,fun he hi => hxy (hi he)⟩
    rw [heq]
    exact pair_collision_probability x y hxy
  have hc : ((bad S).card:ℝ)≤∑ p∈P, ((bad p).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    _≤(∑ p∈P, ((bad p).card:ℝ))/Fintype.card H := div_le_div_of_nonneg_right hc (by positivity)
    _=∑ p∈P, ((bad p).card:ℝ)/Fintype.card H := Finset.sum_div ..
    _=∑ _p∈P, (2:ℝ)^(-(k:ℤ)) := Finset.sum_congr rfl hp
    _=_ := by rw [Finset.sum_const,Finset.card_powersetCard,nsmul_eq_mul]


theorem clock_boundary (m ell : Nat) (hm : 1≤m) (hl : ell≤m) :
    1-(((2*m:Nat):ℝ)-2*ell+1)^2/(((2*m:Nat):ℝ)+1)^2≤4*ell/(((2*m:Nat):ℝ)+1) := by
  let D : ℝ := ((2*m:Nat):ℝ)+1
  have hp : 0<D := by dsimp [D]; positivity
  have he : 1-(((2*m:Nat):ℝ)-2*ell+1)^2/D^2=
      4*ell/D-4*(ell:ℝ)^2/D^2 := by
    dsimp [D]
    field_simp
    ring
  rw [he]
  exact sub_le_self _ (div_nonneg (by positivity) (sq_nonneg D))

theorem bad_columns (d : Nat) (U : Mat d) (hU : IsUnitary U) (G : Finset (Fin d))
    (hG : ∀ j∈G, ∀ i, U i j=(1:Mat d) i j) :
    hs (U-1)^2≤4*((d:ℝ)-G.card) := by
  classical
  have hcol (j : Fin d) : (∑ i, Complex.normSq (U i j))=1 := by
    have hh := congrArg (fun M : Mat d => (M j j).re) hU.1
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Complex.star_def,
      ←Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Matrix.one_apply_eq,Complex.one_re] using hh
  have hentry (x y : ℂ) : Complex.normSq (x-y)≤2*Complex.normSq x+2*Complex.normSq y := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    nlinarith [sq_nonneg (x.re+y.re),sq_nonneg (x.im+y.im)]
  have hbound (j : Fin d) : (∑ i, Complex.normSq ((U-1) i j))≤4 := by
    calc
      _≤∑ i, (2*Complex.normSq (U i j)+2*Complex.normSq ((1:Mat d) i j)) :=
        Finset.sum_le_sum (fun i _ => hentry _ _)
      _=4 := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hcol]
        norm_num [Matrix.one_apply]
  have hzero (j : Fin d) (hj : j∈G) : (∑ i, Complex.normSq ((U-1) i j))=0 := by
    simp only [Matrix.sub_apply,hG j hj,sub_self,Complex.normSq_zero,Finset.sum_const_zero]
  rw [hs_eq_hsNorm,hsNorm_sq,hsSquared,Finset.sum_comm]
  calc
    _=∑ j∈Gᶜ, ∑ i, Complex.normSq ((U-1) i j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact hzero j (by simpa using hj)
    _≤∑ _j∈Gᶜ, (4:ℝ) := Finset.sum_le_sum (fun j _ => hbound j)
    _=4*((d:ℝ)-G.card) := by
      have hc : G.card≤d := by simpa using Finset.card_le_univ G
      rw [Finset.sum_const,Finset.card_compl,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_sub hc]
      ring

def phaseSign (s : Bool) : ℂ := if s then -1 else 1

theorem phaseSign_add (s t : Bool) : phaseSign (s+t)=phaseSign s*phaseSign t := by
  cases s <;> cases t <;> norm_num [phaseSign,Bool.add_eq_xor]

theorem phaseSign_star (s : Bool) : star (phaseSign s)=phaseSign s := by
  cases s <;> norm_num [phaseSign]

def registerDot {α : Type} [Fintype α] (a b : α → Bool) : Bool := ∑ i, a i*b i

theorem registerDot_add_left {α : Type} [Fintype α] (a b c : α → Bool) :
    registerDot (a+b) c=registerDot a c+registerDot b c := by
  simp [registerDot,add_mul,Finset.sum_add_distrib]

theorem registerDot_add_right {α : Type} [Fintype α] (a b c : α → Bool) :
    registerDot a (b+c)=registerDot a b+registerDot a c := by
  simp [registerDot,mul_add,Finset.sum_add_distrib]

/-- A Pauli register on the computational basis, with the X factors before Z. -/
def registerPauli {α : Type} [Fintype α] (s : Bool) (a b : α → Bool) :
    Matrix (α → Bool) (α → Bool) ℂ :=
  fun v w => if v+a=w then phaseSign (s+registerDot b w) else 0

theorem registerPauli_one {α : Type} [Fintype α] [DecidableEq α] :
    registerPauli (α:=α) 0 0 0=1 := by
  classical
  funext v w
  have hz : registerDot (0:α → Bool) w=0 := by simp [registerDot]
  change (if v+(0:α → Bool)=w then phaseSign (0+registerDot 0 w) else 0)=_
  rw [hz,add_zero,zero_add]
  by_cases h : v=w <;> simp [h,phaseSign,Matrix.one_apply]

theorem registerPauli_mul {α : Type} [Fintype α] [DecidableEq α] (s t : Bool) (a b c d : α → Bool) :
    registerPauli s a b*registerPauli t c d=
      registerPauli (s+t+registerDot b c) (a+c) (b+d) := by
  classical
  ext v w
  simp only [Matrix.mul_apply,registerPauli,ite_mul,zero_mul]
  simp only [@eq_comm _ (v+a)]
  rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ (v+a))]
  by_cases hw : v+a+c=w
  · have he : registerDot b (v+a)=registerDot b c+registerDot b w := by
      rw [←hw]
      simp only [registerDot_add_right]
      cases registerDot b v <;> cases registerDot b a <;> cases registerDot b c <;> rfl
    rw [if_pos hw,if_pos (show v+(a+c)=w from by simpa only [add_assoc] using hw)]
    rw [he,←phaseSign_add,registerDot_add_left]
    congr 1
    ring
  · have hw' : v+(a+c)≠w := by simpa only [add_assoc] using hw
    rw [if_neg hw,if_neg hw',mul_zero]

theorem registerPauli_adjoint {α : Type} [Fintype α] [DecidableEq α] (s : Bool) (a b : α → Bool) :
    (registerPauli s a b).conjTranspose=registerPauli (s+registerDot b a) a b := by
  classical
  ext v w
  simp only [Matrix.conjTranspose_apply,registerPauli]
  have he : w+a=v ↔ v+a=w := by
    constructor <;> intro h
    · rw [←h]; ext i; simp [Bool.add_eq_xor,Bool.xor_assoc]
    · rw [←h]; ext i; simp [Bool.add_eq_xor,Bool.xor_assoc]
  by_cases hv : v+a=w
  · rw [if_pos hv,if_pos (he.mpr hv),phaseSign_star,←hv,registerDot_add_right]
    congr 1
    cases s <;> cases registerDot b v <;> cases registerDot b a <;> rfl
  · rw [if_neg hv,if_neg (fun h => hv (he.mp h)),star_zero]

theorem registerPauli_unitary {α : Type} [Fintype α] [DecidableEq α] (s : Bool) (a b : α → Bool) :
    (registerPauli s a b).conjTranspose*registerPauli s a b=1 ∧
      registerPauli s a b*(registerPauli s a b).conjTranspose=1 := by
  rw [registerPauli_adjoint,registerPauli_mul,registerPauli_mul]
  have ha : a+a=0 := by ext i; exact BooleanRing.add_self (a i)
  have hb : b+b=0 := by ext i; exact BooleanRing.add_self (b i)
  have hs : s+registerDot b a+s+registerDot b a=0 := by
    cases s <;> cases registerDot b a <;> rfl
  have ht : s+(s+registerDot b a)+registerDot b a=0 := by
    cases s <;> cases registerDot b a <;> rfl
  rw [ha,hb,hs,ht,registerPauli_one]
  exact ⟨rfl,rfl⟩

def hashPush {α β : Type} [Fintype α] [DecidableEq β] (eta : α → β) (a : α → Bool)
    (c : β) : Bool := ∑ w, if eta w=c then a w else 0

theorem hashPush_zero {α β : Type} [Fintype α] [DecidableEq β] (eta : α → β) :
    hashPush eta 0=0 := by
  ext c
  simp [hashPush]

theorem hashPush_add {α β : Type} [Fintype α] [DecidableEq β]
    (eta : α → β) (a b : α → Bool) : hashPush eta (a+b)=hashPush eta a+hashPush eta b := by
  ext c
  simp only [hashPush,Pi.add_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  split <;> simp_all

theorem hashPush_covariant {α β : Type} [Fintype α] [DecidableEq β]
    (eta : α → β) (g : α ≃ α) (a : α → Bool) :
    hashPush (eta ∘ g) a=hashPush eta (a ∘ g.symm) := by
  ext c
  unfold hashPush
  simpa only [Function.comp_apply,g.symm_apply_apply] using
    (g.sum_comp (fun w => if eta w=c then a (g.symm w) else 0))

theorem hashPush_dot {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (eta : α → β) (S : Finset α) (hinj : Set.InjOn eta (S:Set α))
    (a b : α → Bool) (ha : ∀ w, a w≠0 → w∈S) (hb : ∀ w, b w≠0 → w∈S) :
    registerDot (hashPush eta a) (hashPush eta b)=registerDot a b := by
  classical
  have he (v w : α) : (if eta v=eta w then a v*b w else 0)=
      (if v=w then a v*b w else 0) := by
    by_cases hav : a v=0
    · simp [hav]
    by_cases hbw : b w=0
    · simp [hbw]
    have hh : eta v=eta w ↔ v=w := ⟨fun h => hinj (ha v hav) (hb w hbw) h,congrArg eta⟩
    simp only [hh]
  calc
    _=∑ c, ∑ v, ∑ w, (if eta v=c then a v else 0)*(if eta w=c then b w else 0) := by
      unfold registerDot
      apply Finset.sum_congr rfl
      intro c _
      unfold hashPush
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _=∑ v, ∑ w, ∑ c, (if eta v=c then a v else 0)*(if eta w=c then b w else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
    _=∑ v, ∑ w, if eta v=eta w then a v*b w else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      simp only [ite_mul,zero_mul]
      simp only [@eq_comm _ (eta v)]
      rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ (eta v))]
      by_cases h : eta v=eta w <;> simp [h,Ne.symm]
    _=∑ v, ∑ w, if v=w then a v*b w else 0 := by simp_rw [he]
    _=registerDot a b := by simp [registerDot,eq_comm]

def hashedPauli {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (eta : α → β) (s : Bool) (a b : α → Bool) : Matrix (β → Bool) (β → Bool) ℂ :=
  registerPauli s (hashPush eta a) (hashPush eta b)

/-- Hashing preserves the Pauli product whenever the two crossing masks have no collisions. -/
theorem hashedPauli_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (eta : α → β) (S : Finset α) (hinj : Set.InjOn eta (S:Set α))
    (s t : Bool) (a b c d : α → Bool)
    (hb : ∀ w, b w≠0 → w∈S) (hc : ∀ w, c w≠0 → w∈S) :
    hashedPauli eta s a b*hashedPauli eta t c d=
      hashedPauli eta (s+t+registerDot b c) (a+c) (b+d) := by
  simp only [hashedPauli,registerPauli_mul,hashPush_add,hashPush_dot eta S hinj b c hb hc]

theorem hashedPauli_central {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (eta : α → β) : hashedPauli eta true 0 0= -(1:Matrix (β → Bool) (β → Bool) ℂ) := by
  classical
  ext v w
  by_cases h : v=w <;>
    simp [hashedPauli,hashPush_zero,registerPauli,registerDot,phaseSign,Matrix.one_apply,h]

theorem hashedPauli_unitary {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (eta : α → β) (s : Bool) (a b : α → Bool) :
    (hashedPauli eta s a b).conjTranspose*hashedPauli eta s a b=1 ∧
      hashedPauli eta s a b*(hashedPauli eta s a b).conjTranspose=1 :=
  registerPauli_unitary s (hashPush eta a) (hashPush eta b)

theorem hashedPauli_covariant {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (eta : α → β) (g : α ≃ α) (s : Bool) (a b : α → Bool) :
    hashedPauli (eta ∘ g) s a b=hashedPauli eta s (a ∘ g.symm) (b ∘ g.symm) := by
  simp only [hashedPauli,hashPush_covariant]

def siteMask {α : Type} [DecidableEq α] (v w : α) : Bool := if w=v then 1 else 0

theorem hashPush_site {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (eta : α → β) (v : α) : hashPush eta (siteMask v)=siteMask (eta v) := by
  ext c
  unfold hashPush
  have he (w : α) : (if eta w=c then siteMask v w else 0)=
      (if w=v then siteMask (eta v) c else 0) := by
    by_cases hw : w=v
    · subst w
      simp only [siteMask,ite_eq_left rfl]
      by_cases hc : eta v=c
      · simp [hc]
      · simp [hc,Ne.symm hc]
    · simp [siteMask,hw]
  simp_rw [he]
  simp

theorem registerDot_site {α : Type} [Fintype α] [DecidableEq α]
    (v : α) (a : α → Bool) : registerDot (siteMask v) a=a v := by
  simp [registerDot,siteMask,ite_mul]

theorem registerPauli_central {α : Type} [Fintype α] [DecidableEq α] :
    registerPauli (α:=α) true 0 0= -(1:Matrix (α → Bool) (α → Bool) ℂ) := by
  classical
  funext v w
  by_cases h : v=w <;> simp [registerPauli,registerDot,phaseSign,Matrix.one_apply,h]

/-- The individual hashed lamps square to I and their commutator is exactly -I. -/
theorem hashedPauli_site_exact {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (eta : α → β) (v : α) :
    let X := hashedPauli eta 0 (siteMask v) 0
    let Z := hashedPauli eta 0 0 (siteMask v)
    X*X=1 ∧ Z*Z=1 ∧ X*Z*X*Z= -1 := by
  dsimp only
  simp only [hashedPauli,hashPush_site,hashPush_zero]
  let a := siteMask (eta v)
  have ha : a+a=0 := by ext i; exact BooleanRing.add_self (a i)
  have hdot : registerDot a a=1 := by simp [a,registerDot_site,siteMask]
  have hz (b : β → Bool) : registerDot 0 b=0 := by simp [registerDot]
  have hz' (b : β → Bool) : registerDot b 0=0 := by simp [registerDot]
  change registerPauli 0 a 0*registerPauli 0 a 0=1 ∧
    registerPauli 0 0 a*registerPauli 0 0 a=1 ∧
    registerPauli 0 a 0*registerPauli 0 0 a*registerPauli 0 a 0*registerPauli 0 0 a= -1
  simp only [registerPauli_mul,hz,hz',hdot,zero_add,add_zero,ha]
  exact
    And.intro (registerPauli_one (α:=β))
      (And.intro (registerPauli_one (α:=β)) (registerPauli_central (α:=β)))

theorem hash_family_card (n k : Nat) :
    Fintype.card ((Fin k → Fin n → Bool) × (Fin k → Bool))=2^(k*(n+1)) := by
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [←pow_mul,←pow_add]
  congr 1
  ring

theorem hash_space_card (m k : Nat) :
    Fintype.card ((Fin (2*m+1) × Fin (2*m+1) × Bool) ×
      ((Fin k → Fin (6*m+9) → Bool) × (Fin k → Bool)) × ((Fin k → Bool) → Bool))=
      2*(2*m+1)^2*2^(k*(6*m+10))*2^(2^k) := by
  have hH := hash_family_card (6*m+9) k
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] at hH ⊢
  rw [hH]
  have hn : 6*m+9+1=6*m+10 := by omega
  rw [hn]
  ring

def clockCocycle {G Q : Type} [Group G] [Group Q] (pi : G →* Q) (section_ : Q → G)
    (g : G) (c : Q) : G := (section_ (pi g*c))⁻¹*g*section_ c

theorem clockCocycle_one {G Q : Type} [Group G] [Group Q] (pi : G →* Q) (section_ : Q → G)
    (c : Q) : clockCocycle pi section_ 1 c=1 := by
  simp [clockCocycle]

theorem clockCocycle_mul {G Q : Type} [Group G] [Group Q] (pi : G →* Q) (section_ : Q → G)
    (g h : G) (c : Q) : clockCocycle pi section_ (g*h) c=
      clockCocycle pi section_ g (pi h*c)*clockCocycle pi section_ h c := by
  simp [clockCocycle,mul_assoc]

theorem clockCocycle_inv {G Q : Type} [Group G] [Group Q] (pi : G →* Q) (section_ : Q → G)
    (g : G) (c : Q) : clockCocycle pi section_ g⁻¹ c=
      (clockCocycle pi section_ g ((pi g)⁻¹*c))⁻¹ := by
  simp [clockCocycle,mul_assoc]

theorem clockCocycle_kernel {G Q : Type} [Group G] [Group Q] (pi : G →* Q) (section_ : Q → G)
    (hs : ∀ c, pi (section_ c)=c) (g : G) (c : Q) : pi (clockCocycle pi section_ g c)=1 := by
  simp [clockCocycle,hs,mul_assoc]

/-- The coefficient-and-offset encoding is exactly the space of affine hashes. -/
def hashAffineEquiv (n k : Nat) :
    ((Fin k → Fin n → Bool) × (Fin k → Bool)) ≃
      ((Fin n → Bool) →ᵃ[Bool] (Fin k → Bool)) :=
  (Equiv.prodComm _ _).trans ((Equiv.prodCongr (Equiv.refl _)
    (Matrix.toLin' : Matrix (Fin k) (Fin n) Bool ≃ₗ[Bool] _).toEquiv).trans
      (AffineMap.toConstProdLinearMap Bool).toEquiv.symm)

theorem hashAffineEquiv_apply {n k : Nat}
    (h : (Fin k → Fin n → Bool) × (Fin k → Bool)) (x : Fin n → Bool) :
    hashAffineEquiv n k h x=hashApply h x := by
  ext j
  rw [hash_linear]
  change Matrix.mulVec h.1 x j+h.2 j=h.2 j+∑ i, h.1 j i*x i
  exact add_comm _ _

theorem hashApply_injective {n k : Nat} : Function.Injective (hashApply (n:=n) (k:=k)) := by
  intro h h' hh
  apply (hashAffineEquiv n k).injective
  apply AffineMap.ext
  intro x
  simpa only [hashAffineEquiv_apply] using congrFun hh x

def hashReindex {n k : Nat} (g : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) :
    Equiv.Perm ((Fin k → Fin n → Bool) × (Fin k → Bool)) :=
  (hashAffineEquiv n k).trans ((g.arrowCongrEquiv (AffineEquiv.refl Bool (Fin k → Bool))).trans
    (hashAffineEquiv n k).symm)

theorem hashReindex_apply {n k : Nat} (g : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool))
    (h : (Fin k → Fin n → Bool) × (Fin k → Bool)) (x : Fin n → Bool) :
    hashApply (hashReindex g h) x=hashApply h (g.symm x) := by
  rw [←hashAffineEquiv_apply,hashReindex,Equiv.trans_apply,Equiv.trans_apply,Equiv.apply_symm_apply]
  rw [AffineEquiv.arrowCongrEquiv_apply]
  exact hashAffineEquiv_apply h _

theorem hashReindex_one (n k : Nat) :
    hashReindex (k:=k) (1 : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool))=1 := by
  apply Equiv.ext
  intro h
  apply hashApply_injective
  funext x
  rw [hashReindex_apply]
  rfl

theorem hashReindex_mul {n k : Nat} (g h : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) :
    hashReindex (k:=k) (g*h)=hashReindex g*hashReindex h := by
  apply Equiv.ext
  intro eta
  apply hashApply_injective
  funext x
  simp only [Equiv.Perm.mul_apply,hashReindex_apply]
  rfl

/-- A permutation of blocks, with an independent matrix on every fibre. -/
def blockMatrix {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (tau : Equiv.Perm β) (A : β → Matrix α α ℂ) : Matrix (β × α) (β × α) ℂ :=
  fun i j => if tau i.1=j.1 then A i.1 i.2 j.2 else 0

theorem blockMatrix_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (tau sigma : Equiv.Perm β) (A B : β → Matrix α α ℂ) :
    blockMatrix tau A*blockMatrix sigma B=
      blockMatrix (sigma*tau) (fun b => A b*B (tau b)) := by
  classical
  ext ⟨b,i⟩ ⟨c,j⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,blockMatrix,Equiv.Perm.mul_apply,
    ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [Finset.sum_ite_eq,ite_eq_left (Finset.mem_univ (tau b))]
  by_cases h : sigma (tau b)=c <;> simp [h,Matrix.mul_apply]

theorem blockMatrix_adjoint {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (tau : Equiv.Perm β) (A : β → Matrix α α ℂ) :
    (blockMatrix tau A).conjTranspose=blockMatrix tau.symm (fun b => (A (tau.symm b)).conjTranspose) := by
  classical
  ext ⟨b,i⟩ ⟨c,j⟩
  have he : tau c=b ↔ tau.symm b=c := by
    constructor
    · intro h; rw [←h,tau.symm_apply_apply]
    · intro h; rw [←h,tau.apply_symm_apply]
  by_cases h : tau c=b
  · have hc := he.mp h
    simp [blockMatrix,Matrix.conjTranspose_apply,h,hc]
  · have hc : tau.symm b≠c := fun hh => h (he.mpr hh)
    simp [blockMatrix,Matrix.conjTranspose_apply,h,hc]

theorem blockMatrix_one {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    blockMatrix (1:Equiv.Perm β) (fun _ => (1:Matrix α α ℂ))=1 := by
  classical
  ext ⟨b,i⟩ ⟨c,j⟩
  by_cases h : b=c <;> simp [blockMatrix,Matrix.one_apply,Prod.mk.injEq,h]

theorem blockMatrix_unitary {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (tau : Equiv.Perm β) (A : β → Matrix α α ℂ)
    (hA : ∀ b, (A b).conjTranspose*A b=1 ∧ A b*(A b).conjTranspose=1) :
    (blockMatrix tau A).conjTranspose*blockMatrix tau A=1 ∧
      blockMatrix tau A*(blockMatrix tau A).conjTranspose=1 := by
  rw [blockMatrix_adjoint,blockMatrix_mul,blockMatrix_mul]
  have hleft : (fun b => (A (tau.symm b)).conjTranspose*A (tau.symm b))=fun _ => 1 := by
    funext b
    exact (hA _).1
  have hright : (fun b => A b*(A (tau.symm (tau b))).conjTranspose)=fun _ => 1 := by
    funext b
    simpa only [tau.symm_apply_apply] using (hA b).2
  rw [hleft,hright]
  simp [←Equiv.Perm.inv_def,blockMatrix_one]

theorem hashReindex_symm_apply {n k : Nat}
    (g : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool))
    (eta : (Fin k → Fin n → Bool) × (Fin k → Bool)) (x : Fin n → Bool) :
    hashApply ((hashReindex g).symm eta) x=hashApply eta (g x) := by
  have hh := hashReindex_apply g ((hashReindex (k:=k) g).symm eta) (g x)
  simpa only [Equiv.apply_symm_apply,AffineEquiv.symm_apply_apply] using hh.symm

def hashAction {n k : Nat} (g : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool))
    (s : Bool) (a b : (Fin n → Bool) → Bool) :=
  blockMatrix (hashReindex (k:=k) g).symm (fun eta => hashedPauli (hashApply eta) s a b)

theorem hashAction_unitary {n k : Nat}
    (g : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) (s : Bool) (a b : (Fin n → Bool) → Bool) :
    (hashAction (k:=k) g s a b).conjTranspose*hashAction g s a b=1 ∧
      hashAction (k:=k) g s a b*(hashAction g s a b).conjTranspose=1 :=
  blockMatrix_unitary _ _ (fun eta => hashedPauli_unitary (hashApply eta) s a b)

theorem hashAction_one (n k : Nat) :
    hashAction (k:=k) (1 : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) 0 0 0=1 := by
  have hf : (fun eta : (Fin k → Fin n → Bool) × (Fin k → Bool) =>
      hashedPauli (hashApply eta) 0 0 0)=fun _ => 1 := by
    funext eta
    simp only [hashedPauli,hashPush_zero,registerPauli_one]
  rw [hashAction,hashReindex_one]
  change blockMatrix (1:Equiv.Perm ((Fin k → Fin n → Bool) × (Fin k → Bool))) _=1
  rw [hf]
  exact blockMatrix_one

theorem hashAction_central (n k : Nat) :
    hashAction (k:=k) (1 : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) true 0 0= -1 := by
  classical
  rw [hashAction,hashReindex_one]
  change blockMatrix (1:Equiv.Perm ((Fin k → Fin n → Bool) × (Fin k → Bool))) _= -1
  ext ⟨eta,v⟩ ⟨zeta,w⟩
  by_cases h : eta=zeta <;>
    simp [blockMatrix,hashedPauli_central,Matrix.one_apply,Prod.mk.injEq,h]

/-- The product law on a hash block whose crossing lamps have no collisions. -/
theorem hashAction_mul_row {n k : Nat}
    (g h : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool))
    (s t : Bool) (a b c d : (Fin n → Bool) → Bool)
    (eta : (Fin k → Fin n → Bool) × (Fin k → Bool))
    (S : Finset (Fin n → Bool)) (hinj : Set.InjOn (hashApply eta) (S:Set _))
    (hb : ∀ w, b w≠0 → w∈S) (hc : ∀ w, c (g.symm w)≠0 → w∈S)
    (v : (Fin k → Bool) → Bool)
    (j : ((Fin k → Fin n → Bool) × (Fin k → Bool)) × ((Fin k → Bool) → Bool)) :
    (hashAction (k:=k) g s a b*hashAction (k:=k) h t c d) (eta,v) j=
      hashAction (k:=k) (g*h) (s+t+registerDot b (c ∘ g.symm))
        (a+c ∘ g.symm) (b+d ∘ g.symm) (eta,v) j := by
  have he : hashApply ((hashReindex g).symm eta)=hashApply eta ∘ g := by
    funext x
    exact hashReindex_symm_apply g eta x
  have hp := hashedPauli_mul (hashApply eta) S hinj s t a b (c ∘ g.symm) (d ∘ g.symm) hb hc
  have hf : hashedPauli (hashApply eta) s a b*
      hashedPauli (hashApply ((hashReindex g).symm eta)) t c d=
      hashedPauli (hashApply eta) (s+t+registerDot b (c ∘ g.symm))
        (a+c ∘ g.symm) (b+d ∘ g.symm) := by
    have hcov : hashedPauli (hashApply eta ∘ g) t c d=
        hashedPauli (hashApply eta) t (c ∘ g.symm) (d ∘ g.symm) := by
      convert hashedPauli_covariant (hashApply eta) g.toEquiv t c d using 1
      simp only [AffineEquiv.coe_symm_toEquiv]
    rw [he,hcov]
    exact hp
  rw [hashAction,hashAction,blockMatrix_mul,hashAction,hashReindex_mul]
  simp only [blockMatrix,Equiv.Perm.mul_apply]
  have heq : ((hashReindex (k:=k) g*hashReindex h).symm eta)=
      (hashReindex h).symm ((hashReindex g).symm eta) := rfl
  rw [heq]
  by_cases htest : (hashReindex h).symm ((hashReindex g).symm eta)=j.1
  · simp only [htest,↓reduceIte]
    exact congrFun (congrFun hf v) j.2
  · simp only [htest,↓reduceIte]

theorem blockMatrix_mul_row {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (tau : Equiv.Perm β) (A : β → Matrix α α ℂ) (B : Matrix (β × α) (β × α) ℂ)
    (b : β) (v : α) (j : β × α) :
    (blockMatrix tau A*B) (b,v) j=∑ u, A b v u*B (tau b,u) j := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,blockMatrix,ite_mul,zero_mul,
    Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [Finset.sum_ite_eq,ite_eq_left (Finset.mem_univ (tau b))]

abbrev HashGamma (n : Nat) :=
  ((Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) × Bool ×
    ((Fin n → Bool) → Bool) × ((Fin n → Bool) → Bool)

def hashGammaOne (n : Nat) : HashGamma n := (1,0,0,0)

def hashGammaMul {n : Nat} (x y : HashGamma n) : HashGamma n :=
  (x.1*y.1,x.2.1+y.2.1+registerDot x.2.2.2 (y.2.2.1 ∘ x.1.symm),
    x.2.2.1+y.2.2.1 ∘ x.1.symm,x.2.2.2+y.2.2.2 ∘ x.1.symm)

def hashGammaProduct {n : Nat} : List (HashGamma n) → HashGamma n
  | [] => hashGammaOne n
  | x::xs => hashGammaMul x (hashGammaProduct xs)

def hashGammaSites {n : Nat} (x : HashGamma n) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun w => x.2.2.1 w≠0 ∨ x.2.2.2 w≠0)

def hashProductSites {n : Nat} : List (HashGamma n) → Finset (Fin n → Bool)
  | [] => ∅
  | x::xs => hashGammaSites x ∪ (hashProductSites xs).image x.1

theorem hashGammaProduct_support {n : Nat} (xs : List (HashGamma n)) (w : Fin n → Bool)
    (hw : (hashGammaProduct xs).2.2.1 w≠0 ∨ (hashGammaProduct xs).2.2.2 w≠0) :
    w∈hashProductSites xs := by
  induction xs generalizing w with
  | nil => simp [hashGammaProduct,hashGammaOne] at hw
  | cons x xs ih =>
    simp only [hashGammaProduct,hashGammaMul,Pi.add_apply,Function.comp_apply] at hw
    by_cases hhead : x.2.2.1 w≠0 ∨ x.2.2.2 w≠0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhead⟩)
    · have ha : x.2.2.1 w=0 := by tauto
      have hb : x.2.2.2 w=0 := by tauto
      have ht : x.1.symm w∈hashProductSites xs :=
        ih _ (by simpa only [ha,hb,zero_add] using hw)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x.1.symm w,ht,x.1.apply_symm_apply w⟩)

theorem hashProductSites_card {n : Nat} (xs : List (HashGamma n)) :
    (hashProductSites xs).card≤(xs.map (fun x => (hashGammaSites x).card)).sum := by
  induction xs with
  | nil => simp [hashProductSites]
  | cons x xs ih =>
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left Finset.card_image_le _).trans
      (by simpa only [List.map_cons,List.sum_cons] using Nat.add_le_add_left ih (hashGammaSites x).card))

def hashGammaMatrix {n k : Nat} (x : HashGamma n) := hashAction (k:=k) x.1 x.2.1 x.2.2.1 x.2.2.2

theorem hashGammaProduct_row {n k : Nat} (xs : List (HashGamma n))
    (eta : (Fin k → Fin n → Bool) × (Fin k → Bool))
    (hinj : Set.InjOn (hashApply eta) (hashProductSites xs : Set (Fin n → Bool)))
    (v : (Fin k → Bool) → Bool)
    (j : ((Fin k → Fin n → Bool) × (Fin k → Bool)) × ((Fin k → Bool) → Bool)) :
    (xs.map (hashGammaMatrix (k:=k))).prod (eta,v) j=
      hashGammaMatrix (k:=k) (hashGammaProduct xs) (eta,v) j := by
  induction xs generalizing eta v j with
  | nil => simp only [List.map_nil,List.prod_nil,hashGammaProduct,hashGammaMatrix,hashGammaOne,hashAction_one]
  | cons x xs ih =>
    have himage (w : Fin n → Bool) (hw : w∈hashProductSites xs) : x.1 w∈hashProductSites (x::xs) :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    have htail : Set.InjOn (hashApply ((hashReindex x.1).symm eta)) (hashProductSites xs : Set _) := by
      intro a ha b hb heq
      apply x.1.injective
      apply hinj (himage a ha) (himage b hb)
      simpa only [hashReindex_symm_apply] using heq
    have hb (w : Fin n → Bool) (hw : x.2.2.2 w≠0) : w∈hashProductSites (x::xs) :=
      Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hw⟩)
    have hc (w : Fin n → Bool) (hw : (hashGammaProduct xs).2.2.1 (x.1.symm w)≠0) :
        w∈hashProductSites (x::xs) := by
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨x.1.symm w,hashGammaProduct_support xs _ (Or.inl hw),x.1.apply_symm_apply w⟩)
    rw [List.map_cons,List.prod_cons]
    change (hashAction (k:=k) x.1 x.2.1 x.2.2.1 x.2.2.2*(xs.map (hashGammaMatrix (k:=k))).prod) (eta,v) j=_
    rw [hashAction,blockMatrix_mul_row]
    simp_rw [ih ((hashReindex x.1).symm eta) htail]
    rw [←blockMatrix_mul_row (hashReindex x.1).symm
      (fun zeta => hashedPauli (hashApply zeta) x.2.1 x.2.2.1 x.2.2.2)
      (hashGammaMatrix (k:=k) (hashGammaProduct xs)) eta v j]
    exact hashAction_mul_row x.1 (hashGammaProduct xs).1 x.2.1 (hashGammaProduct xs).2.1
      x.2.2.1 x.2.2.2 (hashGammaProduct xs).2.2.1 (hashGammaProduct xs).2.2.2 eta
      (hashProductSites (x::xs)) hinj hb hc v j

theorem finite_bad_columns {α : Type} [Fintype α] [DecidableEq α] (U : Matrix α α ℂ)
    (hU : U.conjTranspose*U=1 ∧ U*U.conjTranspose=1) (G : Finset α)
    (hG : ∀ j∈G, ∀ i, U i j=(1:Matrix α α ℂ) i j) :
    hsNorm (U-1)^2≤4*((Fintype.card α:ℝ)-G.card) := by
  classical
  have hcol (j : α) : (∑ i, Complex.normSq (U i j))=1 := by
    have hh := congrArg (fun M : Matrix α α ℂ => (M j j).re) hU.1
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Complex.star_def,
      ←Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Matrix.one_apply_eq,Complex.one_re] using hh
  have hentry (x y : ℂ) : Complex.normSq (x-y)≤2*Complex.normSq x+2*Complex.normSq y := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    nlinarith [sq_nonneg (x.re+y.re),sq_nonneg (x.im+y.im)]
  have hbound (j : α) : (∑ i, Complex.normSq ((U-1) i j))≤4 := by
    calc
      _≤∑ i, (2*Complex.normSq (U i j)+2*Complex.normSq ((1:Matrix α α ℂ) i j)) :=
        Finset.sum_le_sum (fun i _ => hentry _ _)
      _=4 := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hcol]
        norm_num [Matrix.one_apply]
  have hzero (j : α) (hj : j∈G) : (∑ i, Complex.normSq ((U-1) i j))=0 := by
    simp only [Matrix.sub_apply,hG j hj,sub_self,Complex.normSq_zero,Finset.sum_const_zero]
  rw [hsNorm_sq,hsSquared,Finset.sum_comm]
  calc
    _=∑ j∈Gᶜ, ∑ i, Complex.normSq ((U-1) i j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact hzero j (by simpa using hj)
    _≤∑ _j∈Gᶜ, (4:ℝ) := Finset.sum_le_sum (fun j _ => hbound j)
    _=4*((Fintype.card α:ℝ)-G.card) := by
      rw [Finset.sum_const,Finset.card_compl,nsmul_eq_mul,Nat.cast_sub (Finset.card_le_univ G)]
      ring

theorem hashGammaMatrix_unitary {n k : Nat} (x : HashGamma n) :
    (hashGammaMatrix (k:=k) x).conjTranspose*hashGammaMatrix x=1 ∧
      hashGammaMatrix (k:=k) x*(hashGammaMatrix x).conjTranspose=1 :=
  hashAction_unitary _ _ _ _

theorem hashGammaMatrices_unitary {n k : Nat} (xs : List (HashGamma n)) :
    ((xs.map (hashGammaMatrix (k:=k))).prod).conjTranspose*(xs.map (hashGammaMatrix (k:=k))).prod=1 ∧
      (xs.map (hashGammaMatrix (k:=k))).prod*((xs.map (hashGammaMatrix (k:=k))).prod).conjTranspose=1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.prod_cons,Matrix.conjTranspose_mul]
    constructor
    · calc
        _=(xs.map (hashGammaMatrix (k:=k))).prod.conjTranspose*
            ((hashGammaMatrix x).conjTranspose*hashGammaMatrix x)*(xs.map hashGammaMatrix).prod := by
          simp only [Matrix.mul_assoc]
        _=1 := by rw [(hashGammaMatrix_unitary x).1,Matrix.mul_one,ih.1]
    · calc
        _=hashGammaMatrix x*((xs.map (hashGammaMatrix (k:=k))).prod*
            (xs.map hashGammaMatrix).prod.conjTranspose)*(hashGammaMatrix x).conjTranspose := by
          simp only [Matrix.mul_assoc]
        _=1 := by rw [ih.2,Matrix.mul_one,(hashGammaMatrix_unitary x).2]

theorem hashGammaProduct_identity_row {n k : Nat} (xs : List (HashGamma n))
    (hprod : hashGammaProduct xs=hashGammaOne n)
    (eta : (Fin k → Fin n → Bool) × (Fin k → Bool))
    (hinj : Set.InjOn (hashApply eta) (hashProductSites xs : Set (Fin n → Bool)))
    (v : (Fin k → Bool) → Bool)
    (j : ((Fin k → Fin n → Bool) × (Fin k → Bool)) × ((Fin k → Bool) → Bool)) :
    (xs.map (hashGammaMatrix (k:=k))).prod (eta,v) j=(1:Matrix _ _ ℂ) (eta,v) j := by
  have hh := hashGammaProduct_row xs eta hinj v j
  simpa only [hprod,hashGammaMatrix,hashGammaOne,hashAction_one] using hh

/-- The exact collision-free rows give the normalized Hilbert--Schmidt error bound. -/
theorem hashGammaProduct_defect {n k : Nat} (xs : List (HashGamma n))
    (hprod : hashGammaProduct xs=hashGammaOne n) :
    hsNorm ((xs.map (hashGammaMatrix (k:=k))).prod-1)^2≤
      4*((hashProductSites xs).card.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ))*
        Fintype.card (((Fin k → Fin n → Bool) × (Fin k → Bool)) × ((Fin k → Bool) → Bool)) := by
  classical
  let H := (Fin k → Fin n → Bool) × (Fin k → Bool)
  let V := (Fin k → Bool) → Bool
  let U := (xs.map (hashGammaMatrix (k:=k))).prod
  let bad : Finset H := Finset.univ.filter (fun eta => ¬Set.InjOn (hashApply eta) (hashProductSites xs : Set _))
  let G : Finset (H × V) := badᶜ.product Finset.univ
  have hU := hashGammaMatrices_unitary (k:=k) xs
  have hUd : U.conjTranspose.conjTranspose*U.conjTranspose=1 ∧
      U.conjTranspose*U.conjTranspose.conjTranspose=1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
  have hG : ∀ j∈G, ∀ i, U.conjTranspose i j=(1:Matrix (H × V) (H × V) ℂ) i j := by
    rintro ⟨eta,v⟩ hj ⟨zeta,w⟩
    have hgood : Set.InjOn (hashApply eta) (hashProductSites xs : Set _) := by
      have hmem := (Finset.mem_product.mp hj).1
      simpa only [Finset.mem_compl,bad,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hmem
    have hh := hashGammaProduct_identity_row xs hprod eta hgood v (zeta,w)
    change U (eta,v) (zeta,w)=(1:Matrix (H × V) (H × V) ℂ) (eta,v) (zeta,w) at hh
    change star (U (eta,v) (zeta,w))=(1:Matrix (H × V) (H × V) ℂ) (zeta,w) (eta,v)
    rw [hh]
    simp [Matrix.one_apply,eq_comm]
  have hh := finite_bad_columns U.conjTranspose hUd G hG
  have hnorm : hsNorm (U.conjTranspose-1)=hsNorm (U-1) := by
    have he : U.conjTranspose-1=(U-1).conjTranspose := by
      ext i j
      simp [Matrix.conjTranspose_apply,Matrix.one_apply,eq_comm]
    rw [he]
    exact hsNorm_conjTranspose (U-1)
  rw [hnorm] at hh
  have hcount : (Fintype.card (H × V):ℝ)-G.card=(bad.card:ℝ)*Fintype.card V := by
    dsimp [G]
    rw [Fintype.card_prod,Finset.card_product,Finset.card_univ,Finset.card_compl,
      Nat.cast_mul,Nat.cast_mul,Nat.cast_sub (Finset.card_le_univ bad)]
    ring
  rw [hcount] at hh
  have hp : (0:ℝ)<Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hbad : (bad.card:ℝ)≤((hashProductSites xs).card.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ))*Fintype.card H :=
    (div_le_iff₀ hp).mp (affine_collision n k (hashProductSites xs))
  calc
    _≤4*(bad.card:ℝ)*Fintype.card V := by simpa only [mul_assoc] using hh
    _≤4*(((hashProductSites xs).card.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ))*Fintype.card H)*Fintype.card V := by
      gcongr
    _=_ := by dsimp [H,V]; simp only [Fintype.card_prod,Nat.cast_mul]; ring

def tailShift (c : ℤ) (y : Concrete.Ray × ℤ) : Concrete.Ray × ℤ := (y.1,y.2+c)

def integerPoint (y : Concrete.Point) : Concrete.Ray × ℤ := (y.1,y.2)

/-- The inverse affine action on each ray, continued to all integer heights. -/
def tailMove : Concrete.HostLetter → Concrete.Ray × ℤ → Concrete.Ray × ℤ
  | .p,(.one,h) => (.one,h-1)
  | .p,(.two,h) => (.two,h+1)
  | .pinv,(.one,h) => (.one,h+1)
  | .pinv,(.two,h) => (.two,h-1)
  | .q,(.one,h) => (.one,h-1)
  | .q,(.three,h) => (.three,h+1)
  | .qinv,(.one,h) => (.one,h+1)
  | .qinv,(.three,h) => (.three,h-1)
  | .i,(.two,h) => (.three,h)
  | .i,(.three,h) => (.two,h)
  | _,y => y

theorem tailMove_shift (a : Concrete.HostLetter) (y : Concrete.Ray × ℤ) (c : ℤ) :
    tailMove a (tailShift c y)=tailShift c (tailMove a y) := by
  rcases y with ⟨r,h⟩
  cases a <;> cases r <;> simp [tailMove,tailShift] <;> omega

theorem tailMove_nat (a : Concrete.HostLetter) (y : Concrete.Point) (hy : 0<y.2) :
    tailMove a (integerPoint y)=integerPoint (Concrete.move a y) := by
  rcases y with ⟨r,h⟩
  cases h with
  | zero => omega
  | succ h =>
    cases a <;> cases r <;>
      simp [tailMove,integerPoint,Concrete.move,Concrete.pBackward,Concrete.pForward,
        Concrete.qBackward,Concrete.qForward,Concrete.swapPoint]

def tailTravel : List Concrete.HostLetter → Concrete.Ray × ℤ → Concrete.Ray × ℤ
  | [],y => y
  | a::w,y => tailTravel w (tailMove a y)

theorem tailTravel_shift (w : List Concrete.HostLetter) (y : Concrete.Ray × ℤ) (c : ℤ) :
    tailTravel w (tailShift c y)=tailShift c (tailTravel w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih => simp only [tailTravel,tailMove_shift,ih]

theorem tailTravel_nat (w : List Concrete.HostLetter) (y : Concrete.Point) (hy : w.length+1≤y.2) :
    tailTravel w (integerPoint y)=integerPoint (Concrete.travel w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih =>
    have hh := Concrete.move_height a y
    have hp : 0<y.2 := by simp only [List.length_cons] at hy; omega
    simp only [tailTravel,Concrete.travel,tailMove_nat a y hp]
    exact ih _ (by simp only [List.length_cons] at hy; omega)

theorem tailTravel_of_host_identity (w : List Concrete.HostLetter) (hw : Concrete.hostEval w=1)
    (y : Concrete.Ray × ℤ) : tailTravel w y=y := by
  have ht (r : Concrete.Ray) : Concrete.travel w (r,w.length+2)=(r,w.length+2) := by
    let p : Concrete.Point := (r,w.length+2)
    have hh := Concrete.hostRow_sound w {Concrete.travel w p} p
    rw [hw,Concrete.hostRow_high w p (by simp [p])] at hh
    have he : p=Concrete.travel w p := by
      simpa [Concrete.rowValue,Concrete.parity,Concrete.bit] using hh
    exact he.symm
  have hzero (r : Concrete.Ray) : tailTravel w (r,0)=(r,0) := by
    have hh := tailTravel_nat w (r,w.length+2) (by simp)
    rw [ht] at hh
    have he := tailTravel_shift w (r,0) ((w.length+2:Nat):ℤ)
    simp only [tailShift,zero_add] at he
    dsimp only [integerPoint] at hh
    rw [he] at hh
    have hf : (tailTravel w (r,0)).1=r := congrArg (fun p : Concrete.Ray × ℤ => p.1) hh
    have hc : (tailTravel w (r,0)).2+((w.length+2:Nat):ℤ)=((w.length+2:Nat):ℤ) :=
      congrArg (fun p : Concrete.Ray × ℤ => p.2) hh
    exact Prod.ext hf (by omega)
  rcases y with ⟨r,h⟩
  simpa only [tailShift,zero_add,hzero] using tailTravel_shift w (r,0) h

/-- Extract the host identity directly from the faithful phase/register action. -/
theorem normalAction_host_identity (n : Concrete.NormalForm)
    (hn : ∀ s, Concrete.normalAction n s=s) : Concrete.hostEval n.host=1 := by
  have hx (u : Concrete.Config) : Concrete.parity (fun v => decide (u=v)) n.xs=false := by
    have he := congrFun (congrArg Prod.snd (hn (false,fun _ => false))) u
    simpa [Concrete.normalAction,Concrete.lampAction,Concrete.hostLift] using he
  have hhInv (v : Concrete.Config) : (Concrete.hostEval n.host).symm v=v := by
    have he := congrFun (congrArg Prod.snd (hn (false,fun u => decide (u=v)))) v
    simpa [Concrete.normalAction,Concrete.lampAction,Concrete.hostLift,hx] using he
  apply Equiv.ext
  intro v
  have he := hhInv (Concrete.hostEval n.host v)
  simpa using he.symm

theorem source_word_tail_identity (w : Word)
    (hw : Concrete.gpPlusWordHom (FreeGroup.mk w)=1) (y : Concrete.Ray × ℤ) :
    tailTravel (Concrete.normalForm (w.map (Concrete.decode true))).host y=y := by
  have hperm : Concrete.wordPermutation true w=1 := congrArg Subtype.val hw
  have hn : ∀ s, Concrete.normalAction (Concrete.normalForm (w.map (Concrete.decode true))) s=s := by
    intro s
    rw [←Concrete.normalForm_sound,←Concrete.wordPermutation_eval,hperm]
    rfl
  exact tailTravel_of_host_identity _ (normalAction_host_identity _ hn) y

abbrev Clock := ℤ × ℤ × Bool

def clockTail (c : Clock) : Concrete.Ray × ℤ → Concrete.Ray × ℤ
  | (.one,h) => (.one,h-c.1-c.2.1)
  | (.two,h) => (if c.2.2 then .three else .two,h+c.1)
  | (.three,h) => (if c.2.2 then .two else .three,h+c.2.1)

theorem clockTail_zero (y : Concrete.Ray × ℤ) : clockTail (0,0,false) y=y := by
  rcases y with ⟨r,h⟩
  cases r <;> simp [clockTail]

def clockMove : Concrete.HostLetter → Clock → Clock
  | .p,c => (c.1+1,c.2.1,c.2.2)
  | .pinv,c => (c.1-1,c.2.1,c.2.2)
  | .q,c => (c.1,c.2.1+1,c.2.2)
  | .qinv,c => (c.1,c.2.1-1,c.2.2)
  | .i,c => (c.2.1,c.1,!c.2.2)
  | _,c => c

theorem clockTail_step (a : Concrete.HostLetter) (c : Clock) (y : Concrete.Ray × ℤ) :
    clockTail (clockMove a c) y=clockTail c (tailMove a y) := by
  rcases c with ⟨u,v,j⟩
  rcases y with ⟨r,h⟩
  cases a <;> cases r <;> cases j <;> simp [clockTail,clockMove,tailMove] <;> omega

def clockTravel : List Concrete.HostLetter → Clock → Clock
  | [],c => c
  | a::w,c => clockMove a (clockTravel w c)

theorem clockTail_travel (w : List Concrete.HostLetter) (c : Clock) (y : Concrete.Ray × ℤ) :
    clockTail (clockTravel w c) y=clockTail c (tailTravel w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih => simpa only [clockTravel,clockTail_step,tailTravel] using ih (tailMove a y)

theorem clockTail_injective : Function.Injective clockTail := by
  rintro ⟨a,b,j⟩ ⟨u,v,k⟩ hh
  have htwo := congrFun hh (Concrete.Ray.two,0)
  have hthree := congrFun hh (Concrete.Ray.three,0)
  have ha : a=u := by simpa only [clockTail,zero_add] using congrArg Prod.snd htwo
  have hb : b=v := by simpa only [clockTail,zero_add] using congrArg Prod.snd hthree
  have hj : j=k := by
    have hr := congrArg Prod.fst htwo
    cases j <;> cases k <;> simp_all [clockTail]
  exact Prod.ext ha (Prod.ext hb hj)

theorem clockTravel_of_host_identity (w : List Concrete.HostLetter) (hw : Concrete.hostEval w=1)
    (c : Clock) : clockTravel w c=c := by
  apply clockTail_injective
  funext y
  rw [clockTail_travel,tailTravel_of_host_identity w hw]

theorem source_word_clock_identity (w : Word)
    (hw : Concrete.gpPlusWordHom (FreeGroup.mk w)=1) (c : Clock) :
    clockTravel (Concrete.normalForm (w.map (Concrete.decode true))).host c=c := by
  apply clockTail_injective
  funext y
  rw [clockTail_travel,source_word_tail_identity w hw]

def tailLetterCost : Concrete.HostLetter → Nat
  | .p | .pinv | .q | .qinv => 1
  | _ => 0

def tailCost : List Concrete.HostLetter → Nat
  | [] => 0
  | a::w => tailLetterCost a+tailCost w

theorem tailMove_cost_upper (a : Concrete.HostLetter) (y : Concrete.Ray × ℤ) :
    (tailMove a y).2≤y.2+tailLetterCost a := by
  rcases y with ⟨r,h⟩
  cases a <;> cases r <;> simp [tailMove,tailLetterCost] <;> omega

theorem move_cost_lower (a : Concrete.HostLetter) (y : Concrete.Point) :
    y.2≤(Concrete.move a y).2+tailLetterCost a := by
  rcases y with ⟨r,h⟩
  cases a <;> cases r <;> cases h <;>
    simp [Concrete.move,Concrete.pBackward,Concrete.pForward,Concrete.qBackward,Concrete.qForward,
      Concrete.swapPoint,tailLetterCost] <;> omega

theorem tailTravel_cost_upper (w : List Concrete.HostLetter) (y : Concrete.Ray × ℤ) :
    (tailTravel w y).2≤y.2+tailCost w := by
  induction w generalizing y with
  | nil => simp [tailTravel,tailCost]
  | cons a w ih =>
    have hh := ih (tailMove a y)
    have hm := tailMove_cost_upper a y
    simp only [tailTravel,tailCost,Nat.cast_add]
    omega

/-- A path is safe when its initial and final heights pay for its translation cost. -/
theorem tailTravel_nat_between (w : List Concrete.HostLetter) (y : Concrete.Point)
    (hy : (tailCost w:ℤ)+2≤(y.2:ℤ)+(tailTravel w (integerPoint y)).2) :
    tailTravel w (integerPoint y)=integerPoint (Concrete.travel w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih =>
    have hb := tailTravel_cost_upper (a::w) (integerPoint y)
    have hp : 0<y.2 := by dsimp only [integerPoint] at hb hy; omega
    have hm := move_cost_lower a y
    have hrec : (tailCost w:ℤ)+2≤((Concrete.move a y).2:ℤ)+
        (tailTravel w (integerPoint (Concrete.move a y))).2 := by
      simp only [tailCost,Nat.cast_add,tailTravel,tailMove_nat a y hp] at hy
      omega
    simpa only [tailTravel,Concrete.travel,tailMove_nat a y hp] using ih _ hrec

theorem hostRow_tail_between (w : List Concrete.HostLetter) (y : Concrete.Point)
    (hy : (tailCost w:ℤ)+4≤(y.2:ℤ)+(tailTravel w (integerPoint y)).2) :
    Concrete.hostRow w y=⟨false,[Concrete.travel w y]⟩ := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih =>
    have hb := tailTravel_cost_upper (a::w) (integerPoint y)
    have hp2 : 2≤y.2 := by dsimp only [integerPoint] at hb hy; omega
    have hp : 0<y.2 := by omega
    have hm := move_cost_lower a y
    have hrec : (tailCost w:ℤ)+4≤((Concrete.move a y).2:ℤ)+
        (tailTravel w (integerPoint (Concrete.move a y))).2 := by
      simp only [tailCost,Nat.cast_add,tailTravel,tailMove_nat a y hp] at hy
      omega
    have hn : y≠Concrete.next := by intro h; subst y; simp [Concrete.next] at hp2
    have ho : y≠Concrete.origin := by intro h; subst y; simp [Concrete.origin] at hp2
    cases a
    all_goals simp only [Concrete.hostRow,Concrete.travel,Concrete.move] at *
    all_goals first
      | exact ih _ hrec
      | (rw [ih y hrec]; simp [ho,hn])

/-- A trivial tail action with bounded translation cost has finite point support. -/
theorem hostRow_finite_support (w : List Concrete.HostLetter)
    (hw : ∀ p, tailTravel w p=p) (r : Nat) (hc : tailCost w+4≤2*r)
    (y : Concrete.Point) (hy : r≤y.2) : Concrete.hostRow w y=⟨false,[y]⟩ := by
  have hh : (tailCost w:ℤ)+4≤(y.2:ℤ)+(tailTravel w (integerPoint y)).2 := by
    rw [hw]
    dsimp only [integerPoint]
    omega
  have ht := tailTravel_nat_between w y (by omega)
  rw [hw] at ht
  have he : Concrete.travel w y=y := by
    apply Prod.ext
    · exact (congrArg (fun p : Concrete.Ray × ℤ => p.1) ht).symm
    · have hz := congrArg (fun p : Concrete.Ray × ℤ => p.2) ht
      dsimp only [integerPoint] at hz
      omega
  simpa only [he] using hostRow_tail_between w y hh

theorem clockTravel_append (u v : List Concrete.HostLetter) (c : Clock) :
    clockTravel (u++v) c=clockTravel u (clockTravel v c) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append,clockTravel,ih]

theorem tailCost_append (u v : List Concrete.HostLetter) : tailCost (u++v)=tailCost u+tailCost v := by
  induction u with
  | nil => simp [tailCost]
  | cons a u ih => simp only [List.cons_append,tailCost,ih,Nat.add_assoc]

def inverseHost : Concrete.HostLetter → Concrete.HostLetter
  | .p => .pinv
  | .pinv => .p
  | .q => .qinv
  | .qinv => .q
  | a => a

def inverseHostWord (w : List Concrete.HostLetter) : List Concrete.HostLetter := w.reverse.map inverseHost

theorem clockMove_inverse (a : Concrete.HostLetter) (c : Clock) :
    clockMove (inverseHost a) (clockMove a c)=c := by
  rcases c with ⟨u,v,j⟩
  cases a <;> cases j <;> simp [inverseHost,clockMove]

theorem clockTravel_inverse (w : List Concrete.HostLetter) (c : Clock) :
    clockTravel (inverseHostWord w) (clockTravel w c)=c := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [inverseHostWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      clockTravel_append,clockTravel,clockMove_inverse]
    exact ih

theorem tailCost_inverse (w : List Concrete.HostLetter) : tailCost (inverseHostWord w)=tailCost w := by
  have hi (a : Concrete.HostLetter) : tailLetterCost (inverseHost a)=tailLetterCost a := by cases a <;> rfl
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [inverseHostWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      tailCost_append,tailCost,hi] at *
    omega

def signedHostPower (a ainv : Concrete.HostLetter) (z : ℤ) : List Concrete.HostLetter :=
  if 0≤z then List.replicate z.toNat a else List.replicate (-z).toNat ainv

theorem clockTravel_replicate_p (n : Nat) (c : Clock) :
    clockTravel (List.replicate n .p) c=(c.1+n,c.2.1,c.2.2) := by
  induction n with
  | zero => simp [clockTravel]
  | succ n ih => simp [List.replicate_succ,clockTravel,ih,clockMove,Nat.cast_add,add_assoc]

theorem clockTravel_replicate_pinv (n : Nat) (c : Clock) :
    clockTravel (List.replicate n .pinv) c=(c.1-n,c.2.1,c.2.2) := by
  induction n with
  | zero => simp [clockTravel]
  | succ n ih => simp [List.replicate_succ,clockTravel,ih,clockMove,Nat.cast_add]; omega

theorem clockTravel_replicate_q (n : Nat) (c : Clock) :
    clockTravel (List.replicate n .q) c=(c.1,c.2.1+n,c.2.2) := by
  induction n with
  | zero => simp [clockTravel]
  | succ n ih => simp [List.replicate_succ,clockTravel,ih,clockMove,Nat.cast_add,add_assoc]

theorem clockTravel_replicate_qinv (n : Nat) (c : Clock) :
    clockTravel (List.replicate n .qinv) c=(c.1,c.2.1-n,c.2.2) := by
  induction n with
  | zero => simp [clockTravel]
  | succ n ih => simp [List.replicate_succ,clockTravel,ih,clockMove,Nat.cast_add]; omega

theorem clockTravel_signed_p (z : ℤ) (c : Clock) :
    clockTravel (signedHostPower .p .pinv z) c=(c.1+z,c.2.1,c.2.2) := by
  cases z with
  | ofNat n => simp [signedHostPower,clockTravel_replicate_p]
  | negSucc n => simp [signedHostPower,clockTravel_replicate_pinv]; omega

theorem clockTravel_signed_q (z : ℤ) (c : Clock) :
    clockTravel (signedHostPower .q .qinv z) c=(c.1,c.2.1+z,c.2.2) := by
  cases z with
  | ofNat n => simp [signedHostPower,clockTravel_replicate_q]
  | negSucc n => simp [signedHostPower,clockTravel_replicate_qinv]; omega

theorem tailCost_replicate (n : Nat) (a : Concrete.HostLetter) :
    tailCost (List.replicate n a)=n*tailLetterCost a := by
  induction n with
  | zero => simp [tailCost]
  | succ n ih => simp [List.replicate_succ,tailCost,ih,Nat.add_mul,Nat.add_comm]

theorem tailCost_signed_p (z : ℤ) : tailCost (signedHostPower .p .pinv z)=z.natAbs := by
  cases z <;> simp [signedHostPower,tailCost_replicate,tailLetterCost]

theorem tailCost_signed_q (z : ℤ) : tailCost (signedHostPower .q .qinv z)=z.natAbs := by
  cases z <;> simp [signedHostPower,tailCost_replicate,tailLetterCost]

def clockSection (c : Clock) : List Concrete.HostLetter :=
  signedHostPower .p .pinv c.1 ++ signedHostPower .q .qinv c.2.1 ++ if c.2.2 then [.i] else []

theorem clockSection_clock (c : Clock) : clockTravel (clockSection c) (0,0,false)=c := by
  rcases c with ⟨u,v,j⟩
  cases j <;> simp [clockSection,clockTravel_append,clockTravel_signed_p,clockTravel_signed_q,
    clockTravel,clockMove]

theorem clockSection_cost (c : Clock) : tailCost (clockSection c)=c.1.natAbs+c.2.1.natAbs := by
  rcases c with ⟨u,v,j⟩
  cases j <;> simp [clockSection,tailCost_append,tailCost_signed_p,tailCost_signed_q,tailCost,tailLetterCost]

def hostClockCocycle (a : Concrete.HostLetter) (c : Clock) : List Concrete.HostLetter :=
  inverseHostWord (clockSection (clockMove a c)) ++ [a] ++ clockSection c

theorem hostClockCocycle_clock (a : Concrete.HostLetter) (c : Clock) :
    clockTravel (hostClockCocycle a c) (0,0,false)=(0,0,false) := by
  simp only [hostClockCocycle,clockTravel_append,clockTravel,clockSection_clock]
  have hh := clockTravel_inverse (clockSection (clockMove a c)) (0,0,false)
  simpa only [clockSection_clock] using hh

theorem hostClockCocycle_tail (a : Concrete.HostLetter) (c : Clock) (y : Concrete.Ray × ℤ) :
    tailTravel (hostClockCocycle a c) y=y := by
  have hh := clockTail_travel (hostClockCocycle a c) (0,0,false) y
  rw [hostClockCocycle_clock] at hh
  simpa only [clockTail_zero] using hh.symm

/-- The sharp cutoff used by the finite hash model: no point above 2m+2 moves. -/
theorem hostClockCocycle_support (a : Concrete.HostLetter) (c : Clock) (m : Nat)
    (h1 : c.1.natAbs≤m) (h2 : c.2.1.natAbs≤m)
    (h3 : (clockMove a c).1.natAbs≤m) (h4 : (clockMove a c).2.1.natAbs≤m)
    (y : Concrete.Point) (hy : 2*m+3≤y.2) :
    Concrete.hostRow (hostClockCocycle a c) y=⟨false,[y]⟩ := by
  apply hostRow_finite_support _ (hostClockCocycle_tail a c) (2*m+3) _ y hy
  have ha : tailLetterCost a≤1 := by cases a <;> decide
  simp only [hostClockCocycle,tailCost_append,tailCost_inverse,clockSection_cost,tailCost]
  omega

/-- Full prop:hash-models, with concrete configuration-lamp semantics. -/
theorem general_hash_models (hhash : Published.PauliHashModels)
    (R : List Word) (ell : Nat) (hell : 1≤ell)
    (hL : ∀ r∈R, r.length≤ell) (hR : ∀ r∈R, Concrete.gpPlusWordHom (FreeGroup.mk r)=1)
    (e : ℝ) (he : 0<e) (he1 : e≤1) :
    ∃ d : Nat, 0<d ∧ ∃ U : Nat → Mat d, normalizedRepresentation R U e ∧
      U 5*U 5=1 ∧ U 6*U 6=1 ∧ wordEval U lampJ=-1 ∧
      log2 d≤336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8 ∧
      log2 d≤400*(ell:ℝ)^2/e^2*log2 (2*ell/e) :=
  AHashProof.general_hash_models_of_published hhash R ell hell hL hR e he he1

/-- prop:hash-models, specialized to the exact concrete model words. -/
theorem presentation_hash_models (hhash : Published.PauliHashModels) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    ∃ d : Nat, 0<d ∧ ∃ U : Nat → Mat d,
      normalizedRepresentation (presentationWords inputPresentation) U e ∧
      U (inputPresentation.distinguished+1)=-1 ∧
      log2 d≤400*44^2/e^2*log2 (88/e) := by
  let R := Concrete.sourceModelWords.map FreeGroup.reduce
  have hL : ∀ r∈R, r.length≤44 := by
    intro r hr
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
    exact of_decide_eq_true (List.all_eq_true.mp Concrete.source_relator_length w hw)
  have hR : ∀ r∈R, Concrete.gpPlusWordHom (FreeGroup.mk r)=1 := by
    intro r hr
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    rw [FreeGroup.reduce.self,mk_substituteWords]
    apply Subtype.ext
    exact Concrete.c2_model_words v hv
  obtain ⟨d,hd,U,hU,_,_,hJ,hD⟩ := general_hash_models hhash R 44 (by norm_num) hL hR e he he1
  let V := fun j => wordEval U (Concrete.modelImages j)
  have hV : ∀ j, IsUnitary (V j) := fun j => wordEval_unitary U hU.1 _
  refine ⟨d,hd,V,⟨hV,?_⟩,?_,?_⟩
  · intro r hr
    rw [AWordArea.word_eval_substitution U hU.1]
    have hh := hU.2 (FreeGroup.reduce (substituteWords Concrete.modelImages r))
      (List.mem_map.mpr ⟨substituteWords Concrete.modelImages r,List.mem_map.mpr ⟨r,hr,rfl⟩,rfl⟩)
    have heq : wordEval U (FreeGroup.reduce (substituteWords Concrete.modelImages r))=
        wordEval U (substituteWords Concrete.modelImages r) := by
      rw [←assignmentHom_word U hU.1,FreeGroup.reduce.self,assignmentHom_word]
    rwa [heq] at hh
  · change wordEval U (Concrete.modelImages (inputPresentation.distinguished+1))=-1
    rw [Concrete.model_distinguished_word]
    exact hJ
  · convert hD.2 using 1 <;> norm_num

theorem game_hash_models (hhash : Published.PauliHashModels) (e : ℝ) (he : 0<e) (he1 : e≤1) :
    ∃ d : Nat, 0<d ∧ ∃ U : Nat → Mat (8*d),
      (∀ j, IsUnitary (U j)) ∧
      (∀ k r, relator suppliedGame k=some r → normalizedHS (wordEval U r-1)≤3*e) ∧
      U (suppliedGame.n+1)=-1 ∧ log2 d≤400*44^2/e^2*log2 (88/e) := by
  obtain ⟨d,hd,U,hR,hw,hD⟩ := presentation_hash_models hhash e he he1
  obtain ⟨V,hV,hrel,hJ⟩ := AGadget.extend d hd U e he.le hR hw
  exact ⟨d,hd,V,hV,hrel,hJ,hD⟩

theorem return_three_budget : 9*returnConstant 3≤7100 := by
  have hp : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : (140:ℝ)/99≤Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hi : 1/Real.sqrt (2:ℝ)≤99/140 := (div_le_iff₀ hp).mpr (by nlinarith)
  simp only [one_div] at hi
  have hn2 : 0≤nu 2 ∧ nu 2≤1707/140 := by
    norm_num [nu,div_eq_mul_inv]
    constructor
    · positivity
    · nlinarith
  have hn3 : 0≤nu 3 ∧ nu 3≤1707/70 := by
    norm_num [nu,div_eq_mul_inv]
    constructor
    · positivity
    · nlinarith
  have hr : returnConstant 3=((nu 3)^2+(14+nu 2+nu 3)^2)/4 := by
    norm_num [returnConstant,Finset.sum_range_succ,show nu 1=3 from by norm_num [nu]]
    ring
  rw [hr]
  have h1 := (sq_le_sq₀ hn3.1 (by norm_num : (0:ℝ)≤1707/70)).mpr hn3.2
  have h2 := (sq_le_sq₀ (by linarith : (0:ℝ)≤14+nu 2+nu 3)
    (by norm_num : (0:ℝ)≤14+1707/140+1707/70)).mpr (by linarith : 14+nu 2+nu 3≤14+1707/140+1707/70)
  nlinarith

theorem hash_log_constant : log2 (88*Real.sqrt 7100)≤103/8 := by
  have hp : (0:ℝ)<88*Real.sqrt 7100 := by positivity
  have hpow : (88*Real.sqrt (7100:ℝ))^8≤(2:ℝ)^103 := by
    rw [mul_pow,show (Real.sqrt (7100:ℝ))^8=((Real.sqrt 7100)^2)^4 from by ring,
      Real.sq_sqrt (by norm_num : (0:ℝ)≤7100)]
    norm_num
  have hh := Real.log_le_log (pow_pos hp 8) hpow
  rw [Real.log_pow,Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  nlinarith

theorem small_error_strategy (hhash : Published.PauliHashModels) (eps : ℝ) (he : 0<eps) (he2 : eps≤1/2) :
    ∃ d : Nat, ∃ s : Strategy MainProof.concreteLCS d d,
      s.psi=(((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • (1:Mat d) ∧ 1-eps≤win s ∧
      log2 d≤mainUpperC/eps*log2 (1/eps) := by
  let e := Real.sqrt eps/Real.sqrt 7100
  have hp : 0<Real.sqrt eps := Real.sqrt_pos.mpr he
  have hq : 0<Real.sqrt (7100:ℝ) := by positivity
  have hep : 0<e := div_pos hp hq
  have he1 : e≤1 := by
    apply (div_le_one hq).mpr
    exact Real.sqrt_le_sqrt (by linarith)
  have heq : e^2=eps/7100 := by
    dsimp [e]
    rw [div_pow,Real.sq_sqrt he.le,Real.sq_sqrt (by norm_num : (0:ℝ)≤7100)]
  obtain ⟨d,hd,U,hU,hR,hJ,hD⟩ := game_hash_models hhash e hep he1
  have hdim : 0<8*d := by omega
  obtain ⟨s,hflat,_,_,hw⟩ := MainProof.flat_return_strategy MainProof.concreteLCS (8*d)
    hdim U hU (3*e) (by positivity) hR hJ
  refine ⟨8*d,s,hflat,?_,?_⟩
  · apply le_trans _ hw
    rw [MainProof.concreteLCS_arity,mul_pow,heq]
    have hh := mul_le_mul_of_nonneg_right return_three_budget he.le
    nlinarith
  · have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hL : 1≤log2 (1/eps) := by
      apply (le_div_iff₀ hlog2).mpr
      simpa using Real.log_le_log (by norm_num : (0:ℝ)<2)
        ((le_div_iff₀ he).mpr (by linarith) : (2:ℝ)≤1/eps)
    have hlog : log2 (88/e)=log2 (88*Real.sqrt 7100)+log2 (1/eps)/2 := by
      dsimp [e,log2]
      rw [Real.log_div (by norm_num : (88:ℝ)≠0) (div_ne_zero hp.ne' hq.ne'),
        Real.log_div hp.ne' hq.ne',Real.log_mul (by norm_num : (88:ℝ)≠0) hq.ne',
        Real.log_sqrt he.le,one_div,Real.log_inv]
      ring
    have hmul : log2 (8*d:Nat)=3+log2 d := by
      unfold log2
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (8:ℝ)≠0) (by exact_mod_cast hd.ne' : (d:ℝ)≠0)]
      have h8 : Real.log (8:ℝ)=3*Real.log 2 := by
        convert Real.log_pow (2:ℝ) 3 using 1 <;> norm_num
      rw [h8]
      field_simp
    have hcoeff : 0≤400*44^2/e^2 := by positivity
    have hD' : log2 d≤400*44^2/(eps/7100)*(103/8+log2 (1/eps)/2) := by
      calc
        _≤400*44^2/e^2*log2 (88/e) := hD
        _≤400*44^2/e^2*(103/8+log2 (1/eps)/2) := by
          rw [hlog]
          exact mul_le_mul_of_nonneg_left (by linarith [hash_log_constant]) hcoeff
        _=_ := by rw [heq]
    rw [hmul]
    unfold mainUpperC
    apply (mul_le_mul_iff_left₀ he).mp
    have hd' : log2 d*eps≤5498240000*(103/8+log2 (1/eps)/2) := by
      calc
        _≤(400*44^2/(eps/7100)*(103/8+log2 (1/eps)/2))*eps := mul_le_mul_of_nonneg_right hD' he.le
        _=_ := by field_simp; ring
    change (3+log2 d)*eps≤(74000000000/eps*log2 (1/eps))*eps
    have hr : (74000000000/eps*log2 (1/eps))*eps=74000000000*log2 (1/eps) := by field_simp
    rw [hr]
    nlinarith

end
end Blueprint.AHash

-- ROUND-12 DECLARATION AUDIT
#print axioms Blueprint.AHash.hashApply
#print axioms Blueprint.AHash.xor_fold_sum
#print axioms Blueprint.AHash.hash_linear
#print axioms Blueprint.AHash.collisionHom
#print axioms Blueprint.AHash.hash_collision_iff
#print axioms Blueprint.AHash.collision_surjective
#print axioms Blueprint.AHash.pair_collision_probability
#print axioms Blueprint.AHash.affine_collision
#print axioms Blueprint.AHash.clock_boundary
#print axioms Blueprint.AHash.bad_columns
#print axioms Blueprint.AHash.phaseSign
#print axioms Blueprint.AHash.phaseSign_add
#print axioms Blueprint.AHash.phaseSign_star
#print axioms Blueprint.AHash.registerDot
#print axioms Blueprint.AHash.registerDot_add_left
#print axioms Blueprint.AHash.registerDot_add_right
#print axioms Blueprint.AHash.registerPauli
#print axioms Blueprint.AHash.registerPauli_one
#print axioms Blueprint.AHash.registerPauli_mul
#print axioms Blueprint.AHash.registerPauli_adjoint
#print axioms Blueprint.AHash.registerPauli_unitary
#print axioms Blueprint.AHash.hashPush
#print axioms Blueprint.AHash.hashPush_zero
#print axioms Blueprint.AHash.hashPush_add
#print axioms Blueprint.AHash.hashPush_covariant
#print axioms Blueprint.AHash.hashPush_dot
#print axioms Blueprint.AHash.hashedPauli
#print axioms Blueprint.AHash.hashedPauli_mul
#print axioms Blueprint.AHash.hashedPauli_central
#print axioms Blueprint.AHash.hashedPauli_unitary
#print axioms Blueprint.AHash.hashedPauli_covariant
#print axioms Blueprint.AHash.siteMask
#print axioms Blueprint.AHash.hashPush_site
#print axioms Blueprint.AHash.registerDot_site
#print axioms Blueprint.AHash.registerPauli_central
#print axioms Blueprint.AHash.hashedPauli_site_exact
#print axioms Blueprint.AHash.hash_family_card
#print axioms Blueprint.AHash.hash_space_card
#print axioms Blueprint.AHash.clockCocycle
#print axioms Blueprint.AHash.clockCocycle_one
#print axioms Blueprint.AHash.clockCocycle_mul
#print axioms Blueprint.AHash.clockCocycle_inv
#print axioms Blueprint.AHash.clockCocycle_kernel
#print axioms Blueprint.AHash.hashAffineEquiv
#print axioms Blueprint.AHash.hashAffineEquiv_apply
#print axioms Blueprint.AHash.hashApply_injective
#print axioms Blueprint.AHash.hashReindex
#print axioms Blueprint.AHash.hashReindex_apply
#print axioms Blueprint.AHash.hashReindex_one
#print axioms Blueprint.AHash.hashReindex_mul
#print axioms Blueprint.AHash.blockMatrix
#print axioms Blueprint.AHash.blockMatrix_mul
#print axioms Blueprint.AHash.blockMatrix_adjoint
#print axioms Blueprint.AHash.blockMatrix_one
#print axioms Blueprint.AHash.blockMatrix_unitary
#print axioms Blueprint.AHash.hashReindex_symm_apply
#print axioms Blueprint.AHash.hashAction
#print axioms Blueprint.AHash.hashAction_unitary
#print axioms Blueprint.AHash.hashAction_one
#print axioms Blueprint.AHash.hashAction_central
#print axioms Blueprint.AHash.hashAction_mul_row
#print axioms Blueprint.AHash.blockMatrix_mul_row
#print axioms Blueprint.AHash.HashGamma
#print axioms Blueprint.AHash.hashGammaOne
#print axioms Blueprint.AHash.hashGammaMul
#print axioms Blueprint.AHash.hashGammaProduct
#print axioms Blueprint.AHash.hashGammaSites
#print axioms Blueprint.AHash.hashProductSites
#print axioms Blueprint.AHash.hashGammaProduct_support
#print axioms Blueprint.AHash.hashProductSites_card
#print axioms Blueprint.AHash.hashGammaMatrix
#print axioms Blueprint.AHash.hashGammaProduct_row
#print axioms Blueprint.AHash.finite_bad_columns
#print axioms Blueprint.AHash.hashGammaMatrix_unitary
#print axioms Blueprint.AHash.hashGammaMatrices_unitary
#print axioms Blueprint.AHash.hashGammaProduct_identity_row
#print axioms Blueprint.AHash.hashGammaProduct_defect
#print axioms Blueprint.AHash.tailShift
#print axioms Blueprint.AHash.integerPoint
#print axioms Blueprint.AHash.tailMove
#print axioms Blueprint.AHash.tailMove_shift
#print axioms Blueprint.AHash.tailMove_nat
#print axioms Blueprint.AHash.tailTravel
#print axioms Blueprint.AHash.tailTravel_shift
#print axioms Blueprint.AHash.tailTravel_nat
#print axioms Blueprint.AHash.tailTravel_of_host_identity
#print axioms Blueprint.AHash.normalAction_host_identity
#print axioms Blueprint.AHash.source_word_tail_identity
#print axioms Blueprint.AHash.Clock
#print axioms Blueprint.AHash.clockTail
#print axioms Blueprint.AHash.clockTail_zero
#print axioms Blueprint.AHash.clockMove
#print axioms Blueprint.AHash.clockTail_step
#print axioms Blueprint.AHash.clockTravel
#print axioms Blueprint.AHash.clockTail_travel
#print axioms Blueprint.AHash.clockTail_injective
#print axioms Blueprint.AHash.clockTravel_of_host_identity
#print axioms Blueprint.AHash.source_word_clock_identity
#print axioms Blueprint.AHash.tailLetterCost
#print axioms Blueprint.AHash.tailCost
#print axioms Blueprint.AHash.tailMove_cost_upper
#print axioms Blueprint.AHash.move_cost_lower
#print axioms Blueprint.AHash.tailTravel_cost_upper
#print axioms Blueprint.AHash.tailTravel_nat_between
#print axioms Blueprint.AHash.hostRow_tail_between
#print axioms Blueprint.AHash.hostRow_finite_support
#print axioms Blueprint.AHash.clockTravel_append
#print axioms Blueprint.AHash.tailCost_append
#print axioms Blueprint.AHash.inverseHost
#print axioms Blueprint.AHash.inverseHostWord
#print axioms Blueprint.AHash.clockMove_inverse
#print axioms Blueprint.AHash.clockTravel_inverse
#print axioms Blueprint.AHash.tailCost_inverse
#print axioms Blueprint.AHash.signedHostPower
#print axioms Blueprint.AHash.clockTravel_replicate_p
#print axioms Blueprint.AHash.clockTravel_replicate_pinv
#print axioms Blueprint.AHash.clockTravel_replicate_q
#print axioms Blueprint.AHash.clockTravel_replicate_qinv
#print axioms Blueprint.AHash.clockTravel_signed_p
#print axioms Blueprint.AHash.clockTravel_signed_q
#print axioms Blueprint.AHash.tailCost_replicate
#print axioms Blueprint.AHash.tailCost_signed_p
#print axioms Blueprint.AHash.tailCost_signed_q
#print axioms Blueprint.AHash.clockSection
#print axioms Blueprint.AHash.clockSection_clock
#print axioms Blueprint.AHash.clockSection_cost
#print axioms Blueprint.AHash.hostClockCocycle
#print axioms Blueprint.AHash.hostClockCocycle_clock
#print axioms Blueprint.AHash.hostClockCocycle_tail
#print axioms Blueprint.AHash.hostClockCocycle_support
#print axioms Blueprint.AHash.general_hash_models
#print axioms Blueprint.AHash.presentation_hash_models
#print axioms Blueprint.AHash.game_hash_models
#print axioms Blueprint.AHash.return_three_budget
#print axioms Blueprint.AHash.hash_log_constant
#print axioms Blueprint.AHash.small_error_strategy
