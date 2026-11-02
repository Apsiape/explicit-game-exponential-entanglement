import Mathlib.Logic.Equiv.Bool
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic

/-! Proof port from OpenAI/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-APACHE-2.0-OpenAI and PROVENANCE.json.
Modified: selected generic namespaces, narrowed imports, split modules for Lean 4.35.0. -/

namespace OAI
noncomputable section
set_option maxHeartbeats 800000

namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
abbrev Cycle := Quotient (Equiv.Perm.SameCycle.setoid f)
instance : Fintype (Cycle f) := Fintype.ofFinite _
def cycle (x : O) : Cycle f := Quotient.mk _ x
def members (c : Cycle f) : Finset O := Finset.univ.filter (fun x => cycle f x=c)
@[simp] lemma mem_members {c : Cycle f} {x : O} : x∈members f c ↔ cycle f x=c := by simp [members]
omit [Fintype O] in
lemma cycle_eq {x y : O} : cycle f x=cycle f y ↔ f.SameCycle x y := Quotient.eq
omit [Fintype O] in
@[simp] lemma cycle_apply (x : O) : cycle f (f x)=cycle f x := by
  apply (cycle_eq f).mpr
  simpa only [Equiv.Perm.sameCycle_apply_left] using Equiv.Perm.SameCycle.refl f x
omit [Fintype O] in
lemma cycle_surjective : Function.Surjective (cycle f) := Quotient.mk_surjective
lemma members_nonempty (c : Cycle f) : (members f c).Nonempty := by
  obtain ⟨x,rfl⟩ := cycle_surjective f c
  exact ⟨x,(mem_members f).mpr rfl⟩
lemma mem_of_mem {c : Cycle f} {x : O} (hx : x∈members f c) : f x∈members f c := by
  simpa only [mem_members,cycle_apply] using hx
lemma card_one_fixed {x : O} (h : (members f (cycle f x)).card=1) : f x=x := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
  have hx : x∈members f (cycle f x) := (mem_members f).mpr rfl
  have hf := mem_of_mem f hx
  rw [ha,Finset.mem_singleton] at hx hf
  exact hf.trans hx.symm
lemma card_le_two_square {x : O} (h : (members f (cycle f x)).card≤2) : f (f x)=x := by
  by_contra hn
  have hfx : f x≠x := fun he => hn (by rw [he,he])
  have hff : f (f x)≠f x := fun he => hfx (f.injective he)
  have hx : x∈members f (cycle f x) := (mem_members f).mpr rfl
  have hs : {x,f x,f (f x)}⊆members f (cycle f x) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    · exact hx
    · exact mem_of_mem f hx
    · exact mem_of_mem f (mem_of_mem f hx)
  have hc := (Finset.card_le_card hs).trans h
  have he : ({x,f x,f (f x)} : Finset O).card=3 := by
    simp [Ne.symm hfx,Ne.symm hn,Ne.symm hff]
  omega

def fixed : Finset O := Finset.univ.filter (fun x => f x=x)
lemma fixed_le_cycles : (fixed f).card≤Fintype.card (Cycle f) := by
  have hi : Function.Injective (fun x : {x // x∈fixed f} => cycle f x.val) := by
    intro x y he
    apply Subtype.ext
    exact ((cycle_eq f).mp he).eq_of_left ((Finset.mem_filter.mp x.property).2)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hi
lemma singleton_cycles_le_fixed :
    (Finset.univ.filter (fun c : Cycle f => (members f c).card=1)).card≤(fixed f).card := by
  let pick : {c : Cycle f // (members f c).card=1} → {x // x∈fixed f} := fun c =>
    ⟨Quotient.out c.val,by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      apply card_one_fixed f
      have he : cycle f (Quotient.out c.val)=c.val := Quotient.out_eq c.val
      simpa only [he] using c.property⟩
  have hi : Function.Injective pick := by
    intro c d he
    apply Subtype.ext
    have h := congrArg (fun x : {x // x∈fixed f} => cycle f x.val) he
    simpa only [pick,cycle,Quotient.out_eq] using h
  simpa only [Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter] using Fintype.card_le_of_injective pick hi
lemma sum_card : (∑ c : Cycle f,(members f c).card)=Fintype.card O := by
  have h := Finset.card_eq_sum_card_fiberwise (f:=cycle f)
    (s:=Finset.univ) (t:=Finset.univ) (fun _ _ => Finset.mem_univ _)
  exact h.symm
lemma large_count :
    (∑ c∈Finset.univ.filter (fun c : Cycle f => 3≤(members f c).card),(members f c).card)=
     (Finset.univ.filter (fun x : O => 3≤(members f (cycle f x)).card)).card := by
  calc
    _ = (Finset.univ.filter (fun x : O => cycle f x∈Finset.univ.filter
      (fun c : Cycle f => 3≤(members f c).card))).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ (cycle f)
    _ = _ := by congr 1; ext x; simp

end TorsionFreeZeroDivisors.PermutationCycles
namespace TorsionFreeZeroDivisors.PermutationTransport
variable {A B : Type} (e : A ≃ B) (f : Equiv.Perm A)
lemma pow_apply (x : A) (n : ℕ) : (e.permCongr f^n) (e x)=e ((f^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Equiv.Perm.mul_apply,ih,Equiv.permCongr_apply,Equiv.symm_apply_apply]
lemma sameCycle [Finite A] {x y : A} (h : f.SameCycle x y) : (e.permCongr f).SameCycle (e x) (e y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n:ℤ),by rw [zpow_natCast,pow_apply,hn]⟩
lemma involutive (h : Function.Involutive f) : Function.Involutive (e.permCongr f) := by
  intro x
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rw [h,Equiv.apply_symm_apply]
lemma fixed_free (h : ∀x,f x≠x) (x : B) : e.permCongr f x≠x := by
  intro he
  apply h (e.symm x)
  simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using congrArg e.symm he
lemma mul (g : Equiv.Perm A) : e.permCongr (f*g)=e.permCongr f*e.permCongr g := by
  ext x
  simp only [Equiv.Perm.mul_apply,Equiv.permCongr_apply,Equiv.symm_apply_apply]
end TorsionFreeZeroDivisors.PermutationTransport
namespace TorsionFreeZeroDivisors.PermutationTransport
open PermutationCycles
variable {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : Equiv.Perm A)
lemma sameCycle_iff (x y : A) : f.SameCycle x y ↔ (e.permCongr f).SameCycle (e x) (e y) := by
  refine ⟨sameCycle e f,?_⟩
  intro h
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast]
  apply e.injective
  rwa [pow_apply] at hn
def cycles : Cycle f ≃ Cycle (e.permCongr f) := Quotient.congr e (sameCycle_iff e f)
lemma card_cycles : Fintype.card (Cycle (e.permCongr f))=Fintype.card (Cycle f) :=
  (Fintype.card_congr (cycles e f)).symm
end TorsionFreeZeroDivisors.PermutationTransport
namespace TorsionFreeZeroDivisors.PermutationCycles
variable {O B : Type} [Fintype O] (f : Equiv.Perm O)
omit [Fintype O] in
lemma invariant_pow (q : O → B) (hq : ∀x,q (f x)=q x) (n : ℕ) (x : O) :
    q ((f^n) x)=q x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hq,ih]
def lift (q : O → B) (hq : ∀x,q (f x)=q x) : Cycle f → B :=
  Quotient.lift q (by
    intro x y h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [←hn]
    exact (invariant_pow f q hq n x).symm)
@[simp] lemma lift_cycle (q : O → B) (hq : ∀x,q (f x)=q x) (x : O) :
    lift f q hq (cycle f x)=q x := rfl
lemma lift_surjective (q : O → B) (hq : ∀x,q (f x)=q x) (hs : Function.Surjective q) :
    Function.Surjective (lift f q hq) := by
  intro b
  obtain ⟨x,rfl⟩ := hs b
  exact ⟨cycle f x,rfl⟩
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.InsertedRotation
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (p : O)

def rotation : Equiv.Perm (O⊕Bool) :=
  Equiv.sumCongr σ (Equiv.refl _) * Equiv.swap (.inl p) (.inr true) *
    Equiv.swap (.inl p) (.inr false)
def pairing : Equiv.Perm (O⊕Bool) := Equiv.sumCongr α Equiv.boolNot
def face : Equiv.Perm (O⊕Bool) := pairing α * rotation σ p
lemma rotation_left (i : O) (hi : i≠p) : rotation σ p (.inl i)=.inl (σ i) := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hi]
@[simp] lemma rotation_p : rotation σ p (.inl p)=.inr false := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
@[simp] lemma rotation_false : rotation σ p (.inr false)=.inr true := by
  simp [rotation,Equiv.Perm.mul_apply]
@[simp] lemma rotation_true : rotation σ p (.inr true)=.inl (σ p) := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
lemma face_left (i : O) (hi : i≠p) : face σ α p (.inl i)=.inl ((α*σ) i) := by
  simp only [face,Equiv.Perm.mul_apply,rotation_left σ p i hi,pairing,Equiv.sumCongr_apply,Sum.map_inl]
@[simp] lemma face_p : face σ α p (.inl p)=.inr true := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_false : face σ α p (.inr false)=.inr false := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_true : face σ α p (.inr true)=.inl ((α*σ) p) := by
  simp [face,Equiv.Perm.mul_apply,pairing]

def classify : O⊕Bool → Option (Cycle (α*σ))
  | .inl i => some (cycle _ i)
  | .inr false => none
  | .inr true => some (cycle _ p)
lemma classify_invariant (i : O⊕Bool) : classify σ α p (face σ α p i)=classify σ α p i := by
  cases i with
  | inl i =>
    by_cases he : i=p
    · subst i; rw [face_p]; rfl
    · rw [face_left σ α p i he]
      simp only [classify,cycle_apply]
  | inr b => cases b <;> simp only [face_false,face_true,classify,cycle_apply]
lemma classify_surjective : Function.Surjective (classify σ α p) := by
  intro b
  cases b with
  | none => exact ⟨.inr false,rfl⟩
  | some c =>
    obtain ⟨i,rfl⟩ := cycle_surjective (α*σ) c
    exact ⟨.inl i,rfl⟩
variable [Fintype O]
/-- Inserting an ear creates a new face and retains all old face cycles. -/
theorem face_count : Fintype.card (Cycle (α*σ))+1≤Fintype.card (Cycle (face σ α p)) := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (face σ α p)
    (classify σ α p) (classify_invariant σ α p) (classify_surjective σ α p))
  simpa only [Fintype.card_option] using h

end TorsionFreeZeroDivisors.InsertedRotation

namespace TorsionFreeZeroDivisors.SwapCycles

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
abbrev Away := {c : Cycle f // c≠cycle f p ∧ c≠cycle f q}
def classify (x : O) : Option (Away f p q) :=
  if h : cycle f x≠cycle f p ∧ cycle f x≠cycle f q then some ⟨cycle f x,h⟩ else none
lemma classify_apply (x : O) : classify f p q (f x)=classify f p q x := by
  simp only [classify,cycle_apply]
@[simp] lemma classify_p : classify f p q p=none := by simp [classify]
@[simp] lemma classify_q : classify f p q q=none := by simp [classify]
lemma classify_swap (x : O) : classify f p q (Equiv.swap p q x)=classify f p q x := by
  by_cases hp : x=p
  · subst x; simp
  · by_cases hq : x=q
    · subst x; simp
    · rw [Equiv.swap_apply_of_ne_of_ne hp hq]
lemma invariant (x : O) : classify f p q ((Equiv.swap p q*f) x)=classify f p q x := by
  rw [Equiv.Perm.mul_apply,classify_swap,classify_apply]
lemma surjective : Function.Surjective (classify f p q) := by
  intro b
  cases b with
  | none => exact ⟨p,classify_p f p q⟩
  | some c =>
    obtain ⟨x,hx⟩ := cycle_surjective f c.val
    refine ⟨x,?_⟩
    have h : cycle f x≠cycle f p ∧ cycle f x≠cycle f q := hx ▸ c.property
    rw [classify,dite_eq_left h]
    exact congrArg some (Subtype.ext hx)
variable [Fintype O]
lemma lower : Fintype.card (Away f p q)+1≤Fintype.card (Cycle (Equiv.swap p q*f)) := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (Equiv.swap p q*f)
    (classify f p q) (invariant f p q) (surjective f p q))
  simpa only [Fintype.card_option] using h
lemma away_count : Fintype.card (Cycle f)≤Fintype.card (Away f p q)+2 := by
  let rest : Finset (Cycle f) := Finset.univ.filter (fun c=>c≠cycle f p ∧ c≠cycle f q)
  have hs : (Finset.univ : Finset (Cycle f))⊆rest∪{cycle f p,cycle f q} := by
    intro c _
    by_cases h : c≠cycle f p ∧ c≠cycle f q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · apply Finset.mem_union_right
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : rest.card=Fintype.card (Away f p q) := by
    simp [rest,Fintype.card_subtype]
  rw [Finset.card_univ,hr] at h
  exact h.trans (Nat.add_le_add_left (Finset.card_insert_le _ _) _)
/-- A two-endpoint switch loses at most one permutation cycle. -/
theorem count_le : Fintype.card (Cycle f)≤Fintype.card (Cycle (Equiv.swap p q*f))+1 := by
  have h₁ := lower f p q
  have h₂ := away_count f p q
  omega

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
lemma cycle_swap (h : cycle f p=cycle f q) (x : O) :
    cycle f (Equiv.swap p q x)=cycle f x := by
  by_cases hp : x=p
  · subst x; simpa using h.symm
  · by_cases hq : x=q
    · subst x; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hp hq]

def adjacentClass (x : O) : Option (Cycle f) := if x=p then none else some (cycle f x)
lemma adjacent_fixed : (Equiv.swap p (f p)*f) p=p := by simp
lemma adjacentClass_invariant (x : O) :
    adjacentClass f p ((Equiv.swap p (f p)*f) x)=adjacentClass f p x := by
  by_cases hx : x=p
  · subst x; rw [adjacent_fixed]
  · have hg : (Equiv.swap p (f p)*f) x≠p := by
      intro h
      exact hx ((Equiv.swap p (f p)*f).injective (h.trans (adjacent_fixed f p).symm))
    rw [adjacentClass,ite_eq_right hg,adjacentClass,ite_eq_right hx]
    apply congrArg some
    rw [Equiv.Perm.mul_apply,cycle_swap f p (f p) (cycle_apply f p).symm,cycle_apply]
lemma adjacentClass_surjective (hp : f p≠p) : Function.Surjective (adjacentClass f p) := by
  intro c
  cases c with
  | none => exact ⟨p,by simp [adjacentClass]⟩
  | some c =>
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    by_cases hx : x=p
    · subst x
      exact ⟨f p,by simp [adjacentClass,hp]⟩
    · exact ⟨x,by simp [adjacentClass,hx]⟩

variable [Fintype O]
lemma count_reverse : Fintype.card (Cycle (Equiv.swap p q*f))≤Fintype.card (Cycle f)+1 := by
  simpa only [←mul_assoc,Equiv.swap_mul_self,one_mul] using count_le (Equiv.swap p q*f) p q
/-- Switching the two arrows adjacent to a nonfixed point splits off that point
as one new actual cycle. -/
lemma adjacent_count (hp : f p≠p) :
    Fintype.card (Cycle (Equiv.swap p (f p)*f))=Fintype.card (Cycle f)+1 := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (Equiv.swap p (f p)*f)
    (adjacentClass f p) (adjacentClass_invariant f p) (adjacentClass_surjective f p hp))
  simp only [Fintype.card_option] at h
  exact Nat.le_antisymm (count_reverse f p (f p)) h
lemma adjacent_support (hp : f p≠p) :
    (Equiv.swap p (f p)*f).support.card<f.support.card := by
  have hs : (Equiv.swap p (f p)*f).support⊆f.support.erase p := by
    intro x hx
    simp only [Finset.mem_erase,Equiv.Perm.mem_support] at *
    refine ⟨?_,?_⟩
    · intro he; subst x; exact hx (adjacent_fixed f p)
    · intro he
      have hxp : x≠p := by intro h; subst x; exact hp he
      have hxf : x≠f p := by
        intro h
        have he' : f x=f p := he.trans h
        exact hxp (f.injective he')
      exact hx (by simp [Equiv.Perm.mul_apply,he,Equiv.swap_apply_of_ne_of_ne hxp hxf])
  exact (Finset.card_le_card hs).trans_lt (Finset.card_erase_lt_of_mem (Equiv.Perm.mem_support.mpr hp))

lemma away_same (h : cycle f p=cycle f q) :
    Fintype.card (Cycle f)≤Fintype.card (Away f p q)+1 := by
  let rest : Finset (Cycle f) := Finset.univ.filter (fun c=>c≠cycle f p ∧ c≠cycle f q)
  have hs : (Finset.univ : Finset (Cycle f))⊆rest∪{cycle f p} := by
    intro c _
    by_cases hc : c=cycle f p
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hc)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,by rwa [←h]⟩)
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : rest.card=Fintype.card (Away f p q) := by simp [rest,Fintype.card_subtype]
  simpa [hr] using hh
lemma same_monotone (h : cycle f p=cycle f q) :
    Fintype.card (Cycle f)≤Fintype.card (Cycle (Equiv.swap p q*f)) :=
  (away_same f p q h).trans (lower f p q)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
lemma identity_count : Fintype.card (Cycle (1 : Equiv.Perm O))=Fintype.card O := by
  apply (Fintype.card_of_bijective (f:=cycle (1 : Equiv.Perm O)) ?_).symm
  refine ⟨?_,cycle_surjective _⟩
  intro x y h
  exact ((cycle_eq _).mp h).eq_of_left rfl
/-- The ordinary permutation sign in terms of all cycles, including fixed points. -/
lemma sign_formula (f : Equiv.Perm O) :
    Equiv.Perm.sign f=(-1 : ℤˣ)^(Fintype.card O+Fintype.card (Cycle f)) := by
  have aux : ∀m,∀g : Equiv.Perm O,g.support.card=m →
      Equiv.Perm.sign g=(-1 : ℤˣ)^(Fintype.card O+Fintype.card (Cycle g)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g hg
      by_cases he : g=1
      · subst g
        rw [Equiv.Perm.sign_one,identity_count,←two_mul,pow_mul]
        norm_num
      · obtain ⟨p,hp⟩ : ∃p,g p≠p := by
          by_contra! h
          exact he (Equiv.ext h)
        have hsmall := adjacent_support g p hp
        have hh := ih (Equiv.swap p (g p)*g).support.card (hg ▸ hsmall)
          (Equiv.swap p (g p)*g) rfl
        rw [Equiv.Perm.sign_mul,Equiv.Perm.sign_swap hp.symm,adjacent_count g p hp,
          ←Nat.add_assoc,pow_succ,mul_comm] at hh
        exact mul_right_cancel hh
  exact aux f.support.card f rfl

/-- A switch between distinct positions of one cycle splits it in two. -/
theorem split_count (f : Equiv.Perm O) (p q : O) (hpq : p≠q)
    (h : cycle f p=cycle f q) :
    Fintype.card (Cycle (Equiv.swap p q*f))=Fintype.card (Cycle f)+1 := by
  have hlo := same_monotone f p q h
  have hhi := count_reverse f p q
  have hne : Fintype.card (Cycle (Equiv.swap p q*f))≠Fintype.card (Cycle f) := by
    intro he
    have hs : Equiv.Perm.sign (Equiv.swap p q*f)=Equiv.Perm.sign f := by
      rw [sign_formula,sign_formula,he]
    rw [Equiv.Perm.sign_mul,Equiv.Perm.sign_swap hpq] at hs
    have hn : (-1 : ℤˣ)=1 := mul_right_cancel (hs.trans (one_mul _).symm)
    norm_num at hn
  omega

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
omit [Fintype O] in
lemma face_switch : α*(Equiv.swap p q*σ)=Equiv.swap (α p) (α q)*(α*σ) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply]
  exact (α.injective.swap_apply p q (σ x)).symm
/-- The global sphere Euler lower bound is preserved when one boundary cycle
is split at two distinct positions. This finite statement does not identify
which realized component contains the outer disk in a self-band surgery. -/
theorem split_euler (hpq : p≠q) (h : cycle σ p=cycle σ q)
    (he : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (α*σ))) :
    Fintype.card O+4≤2*Fintype.card (Cycle (Equiv.swap p q*σ))+
      2*Fintype.card (Cycle (α*(Equiv.swap p q*σ))) := by
  have hv := split_count σ p q hpq h
  have hf := count_le (α*σ) (α p) (α q)
  rw [face_switch,hv]
  omega
end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (p q : O)
/-- Switching two distinct cycles joins the two selected positions in one
actual new cycle. The witness follows the old cycle up to its first return. -/
lemma merge_same (h : cycle f p≠cycle f q) :
    (Equiv.swap p q*f).SameCycle p q := by
  have hp : ∃n : ℕ,0<n ∧ (f^n) p=p :=
    ⟨orderOf f,orderOf_pos f,by rw [pow_orderOf_eq_one];rfl⟩
  let n := Nat.find hp
  have hn : 0<n ∧ (f^n) p=p := Nat.find_spec hp
  have hmin : ∀k,0<k → k<n → (f^k) p≠p := by
    intro k hk hkn he
    have hh := Nat.find_min' hp ⟨hk,he⟩
    omega
  have no_q (k : ℕ) : (f^k) p≠q := by
    intro he
    exact h ((cycle_eq f).mpr ⟨(k:ℤ),by simpa only [zpow_natCast] using he⟩)
  have heq : ∀k,k<n → ((Equiv.swap p q*f)^k) p=(f^k) p := by
    intro k
    induction k with
    | zero => intro _;rfl
    | succ k ih =>
      intro hk
      rw [pow_succ',Equiv.Perm.mul_apply,ih (by omega),Equiv.Perm.mul_apply]
      have hf : f ((f^k) p)=(f^(k+1)) p := by rw [pow_succ',Equiv.Perm.mul_apply]
      rw [hf,Equiv.swap_apply_of_ne_of_ne (hmin _ (by omega) hk) (no_q _)]
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast,hm,pow_succ',Equiv.Perm.mul_apply,heq m (by omega),Equiv.Perm.mul_apply]
  have he : f ((f^m) p)=p := by
    rw [←Equiv.Perm.mul_apply,←pow_succ']
    simpa only [hm, Nat.succ_eq_add_one] using hn.2
  rw [he,Equiv.swap_apply_left]

lemma merge_count (h : cycle f p≠cycle f q) :
    Fintype.card (Cycle (Equiv.swap p q*f))+1=Fintype.card (Cycle f) := by
  have hpq : p≠q := by intro he;exact h (he ▸ rfl)
  have hh := split_count (Equiv.swap p q*f) p q hpq ((cycle_eq _).mpr (merge_same f p q h))
  simpa only [←mul_assoc,Equiv.swap_mul_self,one_mul] using hh.symm
end TorsionFreeZeroDivisors.SwapCycles

namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]

def Refines (f g : Equiv.Perm O) : Prop := ∀x y,cycle f x=cycle f y → cycle g x=cycle g y
lemma refines_of_invariant (f g : Equiv.Perm O) (h : ∀x,cycle g (f x)=cycle g x) : Refines f g := by
  intro x y hxy
  exact congrArg (lift f (cycle g) h) hxy

lemma merge_refines (f : Equiv.Perm O) (p q : O) (h : cycle f p≠cycle f q) :
    Refines f (Equiv.swap p q*f) := by
  apply refines_of_invariant
  intro x
  have hs : cycle (Equiv.swap p q*f) p=cycle (Equiv.swap p q*f) q :=
    (cycle_eq _).mpr (merge_same f p q h)
  calc
    cycle (Equiv.swap p q*f) (f x)=cycle (Equiv.swap p q*f) (Equiv.swap p q ((Equiv.swap p q*f) x)) := by simp
    _ = cycle (Equiv.swap p q*f) ((Equiv.swap p q*f) x) := cycle_swap _ p q hs _
    _ = cycle (Equiv.swap p q*f) x := cycle_apply _ _

def merge (f : Equiv.Perm O) (p q : O) : Equiv.Perm O :=
  if cycle f p=cycle f q then f else Equiv.swap p q*f
lemma merge_refines' (f : Equiv.Perm O) (p q : O) : Refines f (merge f p q) := by
  by_cases h : cycle f p=cycle f q
  · simp only [merge,ite_eq_left h];exact fun _ _ h=>h
  · simp only [merge,ite_eq_right h];exact merge_refines f p q h
lemma merge_pair (f : Equiv.Perm O) (p q : O) : cycle (merge f p q) p=cycle (merge f p q) q := by
  by_cases h : cycle f p=cycle f q
  · rw [merge,ite_eq_left h]; exact h
  · rw [merge,ite_eq_right h]; exact (cycle_eq _).mpr (merge_same f p q h)

def forest (σ : Equiv.Perm O) : List (O×O) → Equiv.Perm O
  | []=>σ
  | e::l=>merge (forest σ l) e.1 e.2
def face (σ : Equiv.Perm O) : List (O×O) → Equiv.Perm O
  | []=>σ
  | e::l=>Equiv.swap e.1 e.2*face σ l
lemma face_invariant (σ : Equiv.Perm O) (l : List (O×O)) (x : O) :
    cycle (forest σ l) (face σ l x)=cycle (forest σ l) x := by
  induction l with
  | nil=>exact cycle_apply σ x
  | cons e l ih=>
    change cycle (merge (forest σ l) e.1 e.2) (Equiv.swap e.1 e.2 (face σ l x))=_
    rw [cycle_swap _ _ _ (merge_pair _ _ _)]
    exact merge_refines' _ _ _ _ _ ih
lemma face_refines (σ : Equiv.Perm O) (l : List (O×O)) : Refines (face σ l) (forest σ l) :=
  refines_of_invariant _ _ (face_invariant σ l)

/-- Euler's upper bound for the actual component partition formed by gluing
listed bands. The forest permutation is a computed partition, not a planar input. -/
theorem upper (σ : Equiv.Perm O) (l : List (O×O)) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))≤
      l.length+2*Nat.card (Cycle (forest σ l)) := by
  induction l with
  | nil=>simp only [face,forest,List.length_nil];omega
  | cons e l ih=>
    by_cases h : cycle (forest σ l) e.1=cycle (forest σ l) e.2
    · have hf := count_reverse (face σ l) e.1 e.2
      simp only [face,forest,merge,ite_eq_left h,List.length_cons]
      simp only [←Nat.card_eq_fintype_card] at *
      omega
    · have hc := merge_count (forest σ l) e.1 e.2 h
      have hn : cycle (face σ l) e.1≠cycle (face σ l) e.2 := fun hh=>h (face_refines σ l _ _ hh)
      have hf := merge_count (face σ l) e.1 e.2 hn
      simp only [face,forest,merge,ite_eq_right h,List.length_cons]
      simp only [←Nat.card_eq_fintype_card] at *
      omega
lemma forest_refines (σ : Equiv.Perm O) (l : List (O×O)) : Refines σ (forest σ l) := by
  induction l with
  | nil=>exact fun _ _ h=>h
  | cons e l ih=>exact fun x y h=>merge_refines' (forest σ l) e.1 e.2 x y (ih x y h)
lemma forest_pair (σ : Equiv.Perm O) (l : List (O×O)) (e : O×O) (he : e∈l) :
    cycle (forest σ l) e.1=cycle (forest σ l) e.2 := by
  induction l with
  | nil=>simp at he
  | cons a l ih=>
    rcases List.mem_cons.mp he with rfl|he
    · exact merge_pair _ _ _
    · exact merge_refines' _ _ _ _ _ (ih he)

def Edge (σ : Equiv.Perm O) (l : List (O×O)) (x y : O) : Prop :=
  σ x=y ∨ (x,y)∈l
abbrev Component (σ : Equiv.Perm O) (l : List (O×O)) := Quotient (Relation.EqvGen.setoid (Edge σ l))
def component (σ : Equiv.Perm O) (l : List (O×O)) (x : O) : Component σ l := Quotient.mk _ x
lemma forest_of_component (σ : Equiv.Perm O) (l : List (O×O)) {x y : O}
    (h : component σ l x=component σ l y) : cycle (forest σ l) x=cycle (forest σ l) y := by
  have hxy : Relation.EqvGen (Edge σ l) x y := Quotient.exact h
  clear h
  induction hxy with
  | rel x y h=>
    rcases h with h|h
    · exact forest_refines σ l x y (by rw [←h,cycle_apply])
    · exact forest_pair σ l (x,y) h
  | refl=>rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih ih'=>exact ih.trans ih'

omit [Fintype O] in
lemma invariant_forest {B : Type} (σ : Equiv.Perm O) (l : List (O×O)) (q : O→B)
    (hσ : ∀x,q (σ x)=q x) (hl : ∀e∈l,q e.1=q e.2) : ∀x,q (forest σ l x)=q x := by
  induction l with
  | nil=>exact hσ
  | cons e l ih=>
    have he := hl e (List.mem_cons_self)
    have hi := ih (fun a ha=>hl a (List.mem_cons_of_mem _ ha))
    intro x
    change q (merge (forest σ l) e.1 e.2 x)=q x
    dsimp only [merge]
    split
    · exact hi x
    · change q (Equiv.swap e.1 e.2 (forest σ l x))=q x
      have hs : ∀z,q (Equiv.swap e.1 e.2 z)=q z := by
        intro z
        by_cases hz : z=e.1
        · subst z;rw [Equiv.swap_apply_left];exact he.symm
        · by_cases hz' : z=e.2
          · subst z;rw [Equiv.swap_apply_right];exact he
          · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
      rw [hs,hi]
omit [Fintype O] in
lemma component_invariant (σ : Equiv.Perm O) (l : List (O×O)) (x : O) :
    component σ l (forest σ l x)=component σ l x := by
  apply invariant_forest σ l
  · intro y
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
  · intro e he
    exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (by simpa using he)))
lemma component_of_forest (σ : Equiv.Perm O) (l : List (O×O)) {x y : O}
    (h : cycle (forest σ l) x=cycle (forest σ l) y) : component σ l x=component σ l y :=
  congrArg (lift (forest σ l) (component σ l) (component_invariant σ l)) h

def componentEquiv (σ : Equiv.Perm O) (l : List (O×O)) : Cycle (forest σ l) ≃ Component σ l :=
  Equiv.ofBijective (lift (forest σ l) (component σ l) (component_invariant σ l)) ⟨by
    intro a b he
    obtain ⟨x,rfl⟩ := cycle_surjective (forest σ l) a
    obtain ⟨y,rfl⟩ := cycle_surjective (forest σ l) b
    exact forest_of_component σ l he,
    lift_surjective _ _ _ Quotient.mk_surjective⟩
lemma upper_components (σ : Equiv.Perm O) (l : List (O×O)) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))≤l.length+2*Nat.card (Component σ l) := by
  have h := upper σ l
  rw [Nat.card_congr (componentEquiv σ l)] at h
  exact h
lemma connected_upper (σ : Equiv.Perm O) (l : List (O×O))
    (hc : ∀x y,Relation.EqvGen (Edge σ l) x y) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))≤l.length+2 := by
  let : Subsingleton (Component σ l) := ⟨by
    intro a b
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨y,rfl⟩ := Quotient.mk_surjective b
    exact Quotient.sound (hc x y)⟩
  have hh : Nat.card (Component σ l)≤1 := (Finite.card_le_one_iff_subsingleton).mpr inferInstance
  have := upper_components σ l
  omega
end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
def strip : Equiv.Perm O := Equiv.swap p (α p)*α
omit [Fintype O] in
lemma strip_p : strip α p p=p := by simp [strip]
omit [Fintype O] in
include hi in
lemma strip_q : strip α p (α p)=α p := by simp only [strip,Equiv.Perm.mul_apply,hi p,Equiv.swap_apply_left]
omit [Fintype O] in
include hi in
lemma strip_away (x : O) (hp : x≠p) (hq : x≠α p) : strip α p x=α x := by
  have hxp : α x≠p := by intro h;exact hq ((hi x).symm.trans (congrArg α h))
  have hxq : α x≠α p := α.injective.ne hp
  exact Equiv.swap_apply_of_ne_of_ne hxp hxq
omit [Fintype O] in
include hi in
lemma strip_involutive : Function.Involutive (strip α p) := by
  intro x
  by_cases hp : x=p
  · subst x;rw [strip_p,strip_p]
  · by_cases hq : x=α p
    · subst x;rw [strip_q α hi p,strip_q α hi p]
    · rw [strip_away α hi p x hp hq,strip_away α hi p (α x)]
      · exact hi x
      · intro h;exact hq ((hi x).symm.trans (congrArg α h))
      · exact α.injective.ne hp
include hi in
lemma strip_support : (strip α p).support=α.support\{p,α p} := by
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or,Equiv.Perm.mem_support]
  constructor
  · intro h
    have hp : x≠p := by intro he;subst x;exact h (strip_p α p)
    have hq : x≠α p := by intro he;subst x;exact h (strip_q α hi p)
    exact ⟨by rwa [strip_away α hi p x hp hq] at h,hp,hq⟩
  · rintro ⟨h,hp,hq⟩
    rwa [strip_away α hi p x hp hq]
include hi in
lemma strip_card (hp : α p≠p) : (strip α p).support.card+2=α.support.card := by
  rw [strip_support α hi p,Finset.card_sdiff_of_subset]
  · have hc : ({p,α p} : Finset O).card=2 := by simp [Ne.symm hp]
    have hs : {p,α p}⊆α.support := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact Equiv.Perm.mem_support.mpr hp
      · exact Equiv.Perm.mem_support.mpr (by rw [hi];exact Ne.symm hp)
    have hh := Finset.card_le_card hs
    rw [hc] at *
    omega
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact Equiv.Perm.mem_support.mpr hp
    · exact Equiv.Perm.mem_support.mpr (by rw [hi];exact Ne.symm hp)

include hi in
/-- Every finite involution is literally a product of its own nontrivial
paired-edge swaps, with exactly one factor for each pair. -/
theorem factorization : ∃l : List (O×O),
    (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α ∧
      2*l.length=α.support.card ∧ ∀e∈l,e.1≠e.2 ∧ α e.1=e.2 := by
  generalize hn : α.support.card=n
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih=>
    by_cases hn0 : n=0
    · have hs : α.support=∅ := Finset.card_eq_zero.mp (hn.trans hn0)
      have ha : α=1 := Equiv.Perm.support_eq_empty_iff.mp hs
      refine ⟨[],?_,by simp [←hn,hs],by simp⟩
      simpa using ha.symm
    · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<α.support.card)
      have hp' := Equiv.Perm.mem_support.mp hp
      have hc := strip_card α hi p hp'
      obtain ⟨l,hl,hL,hedge⟩ := ih (strip α p).support.card (by omega)
        (strip α p) (strip_involutive α hi p) rfl
      refine ⟨(p,α p)::l,?_,?_,?_⟩
      · simp only [List.map_cons,List.prod_cons,hl,strip]
        rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
      · simp only [List.length_cons]
        omega
      · intro e he
        rcases List.mem_cons.mp he with rfl|he
        · exact ⟨Ne.symm hp',rfl⟩
        · obtain ⟨hne,heq⟩ := hedge e he
          have hep : e.1≠p := by
            intro hh
            have hy : e.2=p := (heq.symm.trans (congrArg (strip α p) hh)).trans (strip_p α p)
            exact hne (hh.trans hy.symm)
          have heq' : e.1≠α p := by
            intro hh
            have hy : e.2=α p := (heq.symm.trans (congrArg (strip α p) hh)).trans (strip_q α hi p)
            exact hne (hh.trans hy.symm)
          exact ⟨hne,(strip_away α hi p e.1 hep heq').symm.trans heq⟩
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O]
omit [Fintype O] in
lemma product_invariant {B : Type} (l : List (O×O)) (q : O→B)
    (hl : ∀e∈l,q e.1=q e.2) (x : O) :
    q ((l.map (fun e=>Equiv.swap e.1 e.2)).prod x)=q x := by
  induction l with
  | nil=>rfl
  | cons e l ih=>
    have he := hl e List.mem_cons_self
    have hi := ih (fun a ha=>hl a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    have hs : ∀z,q (Equiv.swap e.1 e.2 z)=q z := by
      intro z
      by_cases hz : z=e.1
      · subst z;rw [Equiv.swap_apply_left];exact he.symm
      · by_cases hz' : z=e.2
        · subst z;rw [Equiv.swap_apply_right];exact he
        · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
    rw [hs,hi]
omit [Fintype O] in
lemma face_product (σ : Equiv.Perm O) (l : List (O×O)) :
    face σ l=(l.map (fun e=>Equiv.swap e.1 e.2)).prod*σ := by
  induction l with
  | nil=>simp [face]
  | cons e l ih=>simp only [face,List.map_cons,List.prod_cons,ih,mul_assoc]

def Edge (σ α : Equiv.Perm O) (x y : O) : Prop := σ x=y ∨ α x=y
abbrev Component (σ α : Equiv.Perm O) := Quotient (Relation.EqvGen.setoid (Edge σ α))
def component (σ α : Equiv.Perm O) (x : O) : Component σ α := Quotient.mk _ x
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
omit [Fintype O] in
include he in
lemma component_forest (x : O) : component σ α (forest σ l x)=component σ α x := by
  apply invariant_forest σ l
  · intro y
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
  · intro e h
    exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (he e h)))
include hl in
lemma forest_alpha (x : O) : cycle (forest σ l) (α x)=cycle (forest σ l) x := by
  rw [←hl]
  exact product_invariant l (cycle (forest σ l)) (forest_pair σ l) x
include hl in
lemma forest_component {x y : O} (h : component σ α x=component σ α y) :
    cycle (forest σ l) x=cycle (forest σ l) y := by
  have hxy : Relation.EqvGen (Edge σ α) x y := Quotient.exact h
  clear h
  induction hxy with
  | rel x y h=>
    rcases h with h|h
    · exact forest_refines σ l x y (by rw [←h,cycle_apply])
    · rw [←h,forest_alpha σ α l hl]
  | refl=>rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih ih'=>exact ih.trans ih'

def componentEquiv : Cycle (forest σ l) ≃ Component σ α :=
  Equiv.ofBijective (lift (forest σ l) (component σ α) (component_forest σ α l he)) ⟨by
    intro a b hh
    obtain ⟨x,rfl⟩ := cycle_surjective (forest σ l) a
    obtain ⟨y,rfl⟩ := cycle_surjective (forest σ l) b
    exact forest_component σ α l hl hh,
    lift_surjective _ _ _ Quotient.mk_surjective⟩
include hl he in
lemma upper_factors : Nat.card (Cycle σ)+Nat.card (Cycle (α*σ))≤l.length+2*Nat.card (Component σ α) := by
  have hh := upper σ l
  rw [face_product,hl,Nat.card_congr (componentEquiv σ α l hl he)] at hh
  exact hh

/-- Every finite orientable permutation map obeys the Euler upper bound. This
uses only its actual involution and actual connected-component equivalence;
no topological realization or Euler inequality is assumed. -/
theorem upper (hi : Function.Involutive α) :
    2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))≤α.support.card+4*Nat.card (Component σ α) := by
  obtain ⟨l,hl,hL,he⟩ := PairingFactors.factorization α hi
  have hh := upper_factors σ α l hl (fun e h=>(he e h).2)
  omega
lemma fixedFree_upper (hi : Function.Involutive α) (hf : ∀x,α x≠x) :
    2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))≤Nat.card O+4*Nat.card (Component σ α) := by
  have hs : α.support=Finset.univ := by ext x;simp [Equiv.Perm.mem_support,hf]
  have hh := upper σ α hi
  simpa only [hs,Finset.card_univ,←Nat.card_eq_fintype_card] using hh
lemma connected_upper (hi : Function.Involutive α) (hf : ∀x,α x≠x)
    (hc : ∀x y,Relation.EqvGen (Edge σ α) x y) :
    2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))≤Nat.card O+4 := by
  let : Subsingleton (Component σ α) := ⟨by
    intro a b
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨y,rfl⟩ := Quotient.mk_surjective b
    exact Quotient.sound (hc x y)⟩
  have hh : Nat.card (Component σ α)≤1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
  have := fixedFree_upper σ α hi hf
  omega
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]
/-- A handle is precisely an edge whose endpoints are already in one component
but which merges two distinct face cycles when glued. -/
def handles (σ : Equiv.Perm O) : List (O×O) → ℕ
  | []=>0
  | e::l=>handles σ l+if cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
      cycle (face σ l) e.1≠cycle (face σ l) e.2 then 1 else 0
omit [Fintype O] in
lemma handles_tail (σ : Equiv.Perm O) (e : O×O) (l : List (O×O)) : handles σ l≤handles σ (e::l) := by
  simp only [handles];omega
lemma handles_exact (σ : Equiv.Perm O) (l : List (O×O)) (hd : ∀e∈l,e.1≠e.2) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))+2*handles σ l=
      l.length+2*Nat.card (Cycle (forest σ l)) := by
  induction l with
  | nil=>simp only [face,forest,handles,List.length_nil];omega
  | cons e l ih=>
    have he := hd e List.mem_cons_self
    have hh := ih (fun a ha=>hd a (List.mem_cons_of_mem _ ha))
    by_cases hc : cycle (forest σ l) e.1=cycle (forest σ l) e.2
    · by_cases hf : cycle (face σ l) e.1=cycle (face σ l) e.2
      · have hg := split_count (face σ l) e.1 e.2 he hf
        simp only [←Nat.card_eq_fintype_card] at hg
        have hn : ¬(cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
            cycle (face σ l) e.1≠cycle (face σ l) e.2) := fun h=>h.2 hf
        simp only [face,forest,merge,ite_eq_left hc,handles,ite_eq_right hn,List.length_cons]
        omega
      · have hg := merge_count (face σ l) e.1 e.2 hf
        simp only [←Nat.card_eq_fintype_card] at hg
        simp only [face,forest,merge,ite_eq_left hc,handles,ite_eq_left (And.intro hc hf),List.length_cons]
        omega
    · have hn : cycle (face σ l) e.1≠cycle (face σ l) e.2 := fun hh=>hc (face_refines σ l _ _ hh)
      have hg := merge_count (face σ l) e.1 e.2 hn
      have hj := merge_count (forest σ l) e.1 e.2 hc
      simp only [←Nat.card_eq_fintype_card] at hg hj
      have hn' : ¬(cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
          cycle (face σ l) e.1≠cycle (face σ l) e.2) := fun h=>hc h.1
      simp only [face,forest,merge,ite_eq_right hc,handles,ite_eq_right hn',List.length_cons]
      omega
lemma zero_handles (σ : Equiv.Perm O) (l : List (O×O)) (hd : ∀e∈l,e.1≠e.2)
    (he : l.length+2*Nat.card (Component σ l)≤Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))) :
    handles σ l=0 := by
  have hh := handles_exact σ l hd
  rw [Nat.card_congr (componentEquiv σ l)] at hh
  omega
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
/-- Combinatorial genus zero, including disconnected maps and isolated darts.
This is a definition in permutation data, not an asserted sphere embedding. -/
def GenusZero : Prop :=
  2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))=α.support.card+4*Nat.card (Component σ α)
lemma genusZero_of_lower (hi : Function.Involutive α)
    (h : α.support.card+4*Nat.card (Component σ α)≤2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))) :
    GenusZero σ α := Nat.le_antisymm h (upper σ α hi) |>.symm
lemma genusZero_iff_handles (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (hd : ∀e∈l,e.1≠e.2 ∧ α e.1=e.2) (hL : 2*l.length=α.support.card) :
    GenusZero σ α ↔ handles σ l=0 := by
  have hh := handles_exact σ l (fun e he=>(hd e he).1)
  rw [face_product,hl,Nat.card_congr (componentEquiv σ α l hl (fun e he=>(hd e he).2))] at hh
  dsimp only [GenusZero]
  omega
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
include hi in
lemma strip_edge {x y : O} (hne : x≠y) (he : strip α p x=y) : α x=y := by
  have hxp : x≠p := by
    intro hx
    have hy : y=p := (he.symm.trans (congrArg (strip α p) hx)).trans (strip_p α p)
    exact hne (hx.trans hy.symm)
  have hxq : x≠α p := by
    intro hx
    have hy : y=α p := (he.symm.trans (congrArg (strip α p) hx)).trans (strip_q α hi p)
    exact hne (hx.trans hy.symm)
  exact (strip_away α hi p x hxp hxq).symm.trans he
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler PairingFactors
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
include hi in
/-- Deleting an actual paired edge cannot create a handle in any component. -/
lemma genusZero_strip (hz : GenusZero σ α) (p : O) (hp : α p≠p) : GenusZero σ (strip α p) := by
  obtain ⟨l,hl,hL,he⟩ := factorization (strip α p) (strip_involutive α hi p)
  have he' : ∀e∈(p,α p)::l,e.1≠e.2 ∧ α e.1=e.2 := by
    intro e hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact ⟨Ne.symm hp,rfl⟩
    · exact ⟨(he e hm).1,strip_edge α hi p (he e hm).1 (he e hm).2⟩
  have hl' : (((p,α p)::l).map (fun e=>Equiv.swap e.1 e.2)).prod=α := by
    simp only [List.map_cons,List.prod_cons,hl,strip]
    rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  have hL' : 2*((p,α p)::l).length=α.support.card := by
    have hc := strip_card α hi p hp
    simp only [List.length_cons]
    omega
  have hh := (genusZero_iff_handles σ α ((p,α p)::l) hl' he' hL').mp hz
  have ht : handles σ l=0 := Nat.eq_zero_of_le_zero ((handles_tail σ (p,α p) l).trans_eq hh)
  exact (genusZero_iff_handles σ (strip α p) l hl he hL).mpr ht
omit [Fintype O] in
include hi in
lemma dual_rel {x y : O} (h : Relation.EqvGen (Edge σ α) x y) :
    Relation.EqvGen (Edge (α*σ) α) x y := by
  induction h with
  | rel x y h=>
    rcases h with hs|ha
    · exact Relation.EqvGen.trans x ((α*σ) x) y
        (Relation.EqvGen.rel _ _ (Or.inl rfl))
        (Relation.EqvGen.rel _ _ (Or.inr (by rw [Equiv.Perm.mul_apply,hi];exact hs)))
    · exact Relation.EqvGen.rel _ _ (Or.inr ha)
  | refl=>exact Relation.EqvGen.refl _
  | symm _ _ _ ih=>exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih'=>exact Relation.EqvGen.trans _ _ _ ih ih'
omit [Fintype O] in
include hi in
lemma dual_twice : α*(α*σ)=σ := by
  ext x
  exact hi (σ x)
def dualEquiv : Component σ α ≃ Component (α*σ) α := Quotient.congrRight (fun x y=>⟨
  dual_rel σ α hi,fun h=>by
    have hh := dual_rel (α*σ) α hi h
    rwa [dual_twice σ α hi] at hh⟩)
include hi in
lemma genusZero_dual : GenusZero σ α ↔ GenusZero (α*σ) α := by
  have hc := Nat.card_congr (dualEquiv σ α hi)
  simp only [GenusZero,dual_twice σ α hi]
  omega
include hi in
/-- The actual band splice preserves componentwise combinatorial genus zero,
prior to bypassing its two now-unpaired occurrences. Both the merge and the
split vertex cases are covered by dual edge deletion. -/
theorem genusZero_band (hz : GenusZero σ α) (p : O) (hp : α p≠p) :
    GenusZero (Equiv.swap p (α p)*σ) (strip α p) := by
  have hd := (genusZero_dual σ α hi).mp hz
  have hs := genusZero_strip (α*σ) α hi hd p hp
  have hh := (genusZero_dual (α*σ) (strip α p) (strip_involutive α hi p)).mp hs
  have he : strip α p*(α*σ)=Equiv.swap p (α p)*σ := by
    rw [strip,mul_assoc,dual_twice σ α hi]
  rwa [he] at hh
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.DeleteCycle

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
abbrev Rest := {x : O // x ≠ p}
lemma invariant (h : f p=p) (x : O) : f x ≠ p ↔ x ≠ p := by
  constructor
  · intro hx he; exact hx (he ▸ h)
  · intro hx he; exact hx (f.injective (he.trans h.symm))
def restrict (h : f p=p) : Equiv.Perm (Rest p) := f.subtypePerm (invariant f p h)
lemma restrict_pow (h : f p=p) (x : Rest p) (k : ℕ) :
    ((restrict f p h ^ k) x).val=(f^k) x := by
  simp only [restrict,Equiv.Perm.subtypePerm_pow,Equiv.Perm.subtypePerm_apply]
variable [Fintype O]
lemma restrict_same (h : f p=p) (x y : Rest p) :
    (restrict f p h).SameCycle x y ↔ f.SameCycle x y := by
  constructor
  · intro hs
    obtain ⟨k,hk⟩ := hs.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    exact (restrict_pow f p h x k).symm.trans (congrArg Subtype.val hk)
  · intro hs
    obtain ⟨k,hk⟩ := hs.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    exact (restrict_pow f p h x k).trans hk

def classify (h : f p=p) (x : O) : Option (Cycle (restrict f p h)) :=
  if hx : x=p then none else some (cycle (restrict f p h) ⟨x,hx⟩)
omit [Fintype O] in
lemma classify_apply (h : f p=p) (x : O) : classify f p h (f x)=classify f p h x := by
  by_cases hx : x=p
  · subst x; rw [h]
  · have hfx := (invariant f p h x).mpr hx
    rw [classify,dite_eq_right hfx,classify,dite_eq_right hx]
    apply congrArg some
    exact cycle_apply (restrict f p h) ⟨x,hx⟩
omit [Fintype O] in
lemma classify_surjective (h : f p=p) : Function.Surjective (classify f p h) := by
  intro c
  cases c with
  | none => exact ⟨p,by simp [classify]⟩
  | some c =>
    obtain ⟨x,rfl⟩ := cycle_surjective (restrict f p h) c
    exact ⟨x,by simp [classify,x.property]⟩
lemma classify_eq (h : f p=p) {x y : O} (he : classify f p h x=classify f p h y) : f.SameCycle x y := by
  by_cases hx : x=p
  · subst x
    have hy : y=p := by
      by_contra hy
      simp [classify,hy] at he
    subst y
    exact Equiv.Perm.SameCycle.refl _ _
  · by_cases hy : y=p
    · subst y; simp [classify,hx] at he
    · simp only [classify,dite_eq_right hx,dite_eq_right hy,Option.some.injEq] at he
      exact (restrict_same f p h ⟨x,hx⟩ ⟨y,hy⟩).mp ((cycle_eq _).mp he)
def cycleEquiv (h : f p=p) : Cycle f ≃ Option (Cycle (restrict f p h)) :=
  Equiv.ofBijective (lift f (classify f p h) (classify_apply f p h)) ⟨by
    intro c d he
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    obtain ⟨y,rfl⟩ := cycle_surjective f d
    exact (cycle_eq f).mpr (classify_eq f p h he),
    lift_surjective f _ _ (classify_surjective f p h)⟩
lemma fixed_count (h : f p=p) :
    Fintype.card (Cycle f)=Fintype.card (Cycle (restrict f p h))+1 := by
  simpa only [Fintype.card_option] using Fintype.card_congr (cycleEquiv f p h)

/-- Delete an occurrence by bypassing it in its boundary cycle. -/
def bypass : Equiv.Perm (Rest p) := restrict (Equiv.swap p (f p)*f) p (SwapCycles.adjacent_fixed f p)
lemma bypass_count (h : f p≠p) : Fintype.card (Cycle (bypass f p))=Fintype.card (Cycle f) := by
  have h₁ := fixed_count (Equiv.swap p (f p)*f) p (SwapCycles.adjacent_fixed f p)
  have h₂ := SwapCycles.adjacent_count f p h
  change _=Fintype.card (Cycle (bypass f p))+1 at h₁
  omega
end
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
lemma bypass_apply [Fintype O] (x : Rest p) :
    (bypass f p x).val=Equiv.swap p (f p) (f x) := rfl
/-- Bypassing a point commutes with a left permutation fixing that point. -/
lemma bypass_mul [Fintype O] (a : Equiv.Perm O) (ha : a p=p) :
    bypass (a*f) p=restrict a p ha*bypass f p := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change Equiv.swap p (a (f p)) (a (f x))=a (Equiv.swap p (f p) (f x))
  simpa only [ha] using (a.injective.swap_apply p (f p) (f x))
lemma bypass_nonfixed [Fintype O] (q : Rest p) (hq : f q≠q)
    (hshort : f q=p → f p≠q) : bypass f p q≠q := by
  intro he
  have he := congrArg Subtype.val he
  rw [bypass_apply] at he
  by_cases h : f q=p
  · rw [h,Equiv.swap_apply_left] at he
    exact hshort h he
  · have hh : f q≠f p := fun he=>q.property (f.injective he)
    rw [Equiv.swap_apply_of_ne_of_ne h hh] at he
    exact hq he
variable [Fintype O]
lemma card_rest : Fintype.card (Rest p)+1=Fintype.card O := by
  have h := Fintype.card_subtype_compl (fun x : O=>x=p)
  have he : Fintype.card {x : O // x=p}=1 := Fintype.card_unique
  change Fintype.card (Rest p)=_ at h
  rw [he] at h
  have hn : 0<Fintype.card O := Fintype.card_pos_iff.mpr ⟨p⟩
  omega
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
variable {O B : Type} (σ α : Equiv.Perm O)
lemma component_rotation (x : O) : component σ α (σ x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
lemma component_partner (x : O) : component σ α (α x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl)))
def lift (q : O→B) (hσ : ∀x,q (σ x)=q x) (hα : ∀x,q (α x)=q x) : Component σ α →B :=
  Quotient.lift q (by
    intro x y h
    induction h with
    | rel x y h=>
      rcases h with h|h
      · exact (hσ x).symm.trans (congrArg q h)
      · exact (hα x).symm.trans (congrArg q h)
    | refl=>rfl
    | symm _ _ _ ih=>exact ih.symm
    | trans _ _ _ _ _ ih ih'=>exact ih.trans ih')
@[simp] lemma lift_component (q : O→B) (hσ : ∀x,q (σ x)=q x) (hα : ∀x,q (α x)=q x) (x : O) :
    lift σ α q hσ hα (component σ α x)=q x := rfl
lemma swap_invariant (q : O→B) (p r : O) (h : q p=q r) (x : O) : q (Equiv.swap p r x)=q x := by
  by_cases hp : x=p
  · subst x;rw [Equiv.swap_apply_left];exact h.symm
  · by_cases hr : x=r
    · subst x;rw [Equiv.swap_apply_right];exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hp hr]
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
abbrev rotation := bypass σ p
abbrev partner := restrict α p ha
def push (x : O) : Rest p := if hx : x=p then ⟨σ p,hs⟩ else ⟨x,hx⟩
omit [Fintype O] in
lemma push_p : push σ p hs p=⟨σ p,hs⟩ := by simp [push]
omit [Fintype O] in
lemma push_val (x : Rest p) : push σ p hs x=x := by simp [push,x.property]
lemma push_rotation (x : Rest p) : push σ p hs (σ x)=rotation σ p x := by
  apply Subtype.ext
  rw [bypass_apply]
  by_cases h : σ x=p
  · simp only [push,h,dite_eq_left trivial,Equiv.swap_apply_left]
  · have hn : σ x≠σ p := σ.injective.ne x.property
    simp only [push,dite_eq_right h,Equiv.swap_apply_of_ne_of_ne h hn]
def projectRaw (x : O) : MapEuler.Component (rotation σ p) (partner α p ha) :=
  component (rotation σ p) (partner α p ha) (push σ p hs x)
lemma project_rotation (x : O) : projectRaw σ α p ha hs (σ x)=projectRaw σ α p ha hs x := by
  by_cases hx : x=p
  · subst x
    change component _ _ (push σ p hs (σ p))=component _ _ (push σ p hs p)
    rw [push_p]
    simp only [push,dite_eq_right hs]
  · change component _ _ (push σ p hs (σ (⟨x,hx⟩ : Rest p)))=_
    rw [push_rotation]
    change component _ _ (rotation σ p ⟨x,hx⟩)=component _ _ (push σ p hs (⟨x,hx⟩ : Rest p))
    rw [push_val,component_rotation]
omit [Fintype O] in
lemma project_partner (x : O) : projectRaw σ α p ha hs (α x)=projectRaw σ α p ha hs x := by
  by_cases hx : x=p
  · subst x;rw [ha]
  · have hn : α x≠p := (DeleteCycle.invariant α p ha x).mpr hx
    change component _ _ (push σ p hs (α x))=component _ _ (push σ p hs x)
    simp only [push,dite_eq_right hx,dite_eq_right hn]
    exact component_partner (rotation σ p) (partner α p ha) ⟨x,hx⟩
def project : MapEuler.Component σ α → MapEuler.Component (rotation σ p) (partner α p ha) :=
  MapEuler.lift σ α (projectRaw σ α p ha hs) (project_rotation σ α p ha hs) (project_partner σ α p ha hs)
lemma include_rotation (x : Rest p) : component σ α (rotation σ p x)=component σ α x := by
  rw [bypass_apply,MapEuler.swap_invariant (component σ α) p (σ p) (component_rotation σ α p).symm]
  exact component_rotation σ α x
omit [Fintype O] in
lemma include_partner (x : Rest p) : component σ α (partner α p ha x)=component σ α x :=
  component_partner σ α x
def inclusion : MapEuler.Component (rotation σ p) (partner α p ha) → MapEuler.Component σ α :=
  MapEuler.lift _ _ (fun x : Rest p=>component σ α x) (include_rotation σ α p) (include_partner σ α p ha)
omit [Fintype O] in
lemma component_push (x : O) : component σ α (push σ p hs x)=component σ α x := by
  by_cases hx : x=p
  · subst x;rw [push_p];exact component_rotation σ α p
  · simp only [push,dite_eq_right hx]
lemma left_inverse : Function.LeftInverse (inclusion σ α p ha) (project σ α p ha hs) := by
  intro c
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  exact component_push σ α p hs x
lemma project_surjective : Function.Surjective (project σ α p ha hs) := by
  intro c
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  refine ⟨component σ α x,?_⟩
  change component _ _ (push σ p hs x)=component _ _ x
  rw [push_val]
def componentEquiv : MapEuler.Component σ α ≃ MapEuler.Component (rotation σ p) (partner α p ha) :=
  Equiv.ofBijective (project σ α p ha hs) ⟨(left_inverse σ α p ha hs).injective,project_surjective σ α p ha hs⟩
end
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
def support_equiv : ↥(partner α p ha).support ≃ ↥α.support where
  toFun x := ⟨x.val.val,by
    have h := Equiv.Perm.mem_support.mp x.property
    exact Equiv.Perm.mem_support.mpr (fun he=>h (Subtype.ext he))⟩
  invFun x := ⟨⟨x.val,by
    intro he
    have hn := Equiv.Perm.mem_support.mp x.property
    exact hn (he ▸ ha)⟩,by
      apply Equiv.Perm.mem_support.mpr
      intro he
      exact Equiv.Perm.mem_support.mp x.property (congrArg Subtype.val he)⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
lemma support_count : (partner α p ha).support.card=α.support.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (support_equiv α p ha)
omit [Fintype O] in
include ha in
lemma face_nonfixed (hs : σ p≠p) : (α*σ) p≠p := by
  intro he
  exact hs (α.injective ((show α (σ p)=p from he).trans ha.symm))
/-- Removing a dart fixed by the partner involution preserves all actual map
components and the Euler equality when its vertex is not a singleton. -/
theorem genusZero_delete (hs : σ p≠p) (hz : GenusZero σ α) :
    GenusZero (rotation σ p) (partner α p ha) := by
  have hv := bypass_count σ p hs
  have hf := bypass_count (α*σ) p (face_nonfixed σ α p ha hs)
  rw [bypass_mul σ p α ha] at hf
  have hc := Nat.card_congr (componentEquiv σ α p ha hs)
  have he := support_count α p ha
  simp only [←Nat.card_eq_fintype_card] at hv hf
  dsimp only [GenusZero] at hz ⊢
  change Nat.card (Cycle (rotation σ p))=Nat.card (Cycle σ) at hv
  change Nat.card (Cycle (partner α p ha*rotation σ p))=Nat.card (Cycle (α*σ)) at hf
  rw [hv,hf,←hc]
  have hsup : ∀ (i j : Fintype (Rest p)) (d e : DecidableEq (Rest p)),
      @Equiv.Perm.support (Rest p) d i (partner α p ha) =
      @Equiv.Perm.support (Rest p) e j (partner α p ha) := by
    intro i j d e
    cases Subsingleton.elim i j
    cases Subsingleton.elim d e
    rfl
  convert hz using 1
  rw [←he]
  congr 1
  exact congrArg Finset.card (hsup _ _ _ _)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles DeleteCycle
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
abbrev q' : Rest p := ⟨q,hpq.symm⟩
abbrev Residual := Rest (q' p q hpq)
def adjusted := α*Equiv.swap p q
omit [Fintype O] in
include hi hpair in
lemma adjusted_p : adjusted α p q p=p := by
  rw [adjusted,Equiv.Perm.mul_apply,Equiv.swap_apply_left]
  exact (congrArg α hpair).symm.trans (hi p)
omit [Fintype O] in
include hpair in
lemma adjusted_q : adjusted α p q q=q := by
  rw [adjusted,Equiv.Perm.mul_apply,Equiv.swap_apply_right,hpair]
def α₁ : Equiv.Perm (Rest p) := restrict (adjusted α p q) p (adjusted_p α hi p q hpair)
omit [Fintype O] in
lemma α₁_q : α₁ α hi p q hpair (q' p q hpq)=q' p q hpq := by
  apply Subtype.ext
  exact adjusted_q α p q hpair

def partner : Equiv.Perm (Residual p q hpq) :=
  restrict (α₁ α hi p q hpair) (q' p q hpq) (α₁_q α hi p q hpq hpair)
def switched : Equiv.Perm O := Equiv.swap p q*σ
def rotation : Equiv.Perm (Residual p q hpq) := bypass (bypass (switched σ p q) p) (q' p q hpq)
def face : Equiv.Perm O := α*σ

def val (x : Residual p q hpq) : O := x.val.val
omit [Fintype O] in
lemma val_ne_p (x : Residual p q hpq) : val p q hpq x≠p := x.val.property
omit [Fintype O] in
lemma val_ne_q (x : Residual p q hpq) : val p q hpq x≠q := by
  intro h
  exact x.property (Subtype.ext h)
omit [Fintype O] in
lemma val_injective : Function.Injective (val p q hpq) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)
omit [Fintype O] in
lemma partner_val (x : Residual p q hpq) :
    val p q hpq (partner α hi p q hpq hpair x)=α (val p q hpq x) := by
  change α (Equiv.swap p q (val p q hpq x))=_
  rw [Equiv.swap_apply_of_ne_of_ne (val_ne_p p q hpq x) (val_ne_q p q hpq x)]
omit [Fintype O] in
lemma partner_involutive : Function.Involutive (partner α hi p q hpq hpair) := by
  intro x
  apply val_injective p q hpq
  rw [partner_val,partner_val,hi]
omit [Fintype O] in
include hpair in
lemma partner_distinct (hf : ∀x,α x≠x) (x : Residual p q hpq) : partner α hi p q hpq hpair x≠x := by
  intro he
  have h := congrArg (val p q hpq) he
  rw [partner_val] at h
  exact hf _ h
lemma face_eq : partner α hi p q hpq hpair*rotation σ p q hpq=
    bypass (bypass (face σ α) p) (q' p q hpq) := by
  have he : face σ α=adjusted α p q*switched σ p q := by
    simp only [face,adjusted,switched]
    rw [mul_assoc α (Equiv.swap p q),←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
  rw [he,bypass_mul _ _ _ (adjusted_p α hi p q hpair)]
  change _=bypass (α₁ α hi p q hpair*bypass (switched σ p q) p) (q' p q hpq)
  rw [bypass_mul _ _ _ (α₁_q α hi p q hpq hpair)]
  rfl

variable (hs : σ p≠p) (hfp : face σ α p≠p) (hfq : face σ α q≠q)
omit [Fintype O] in
include hi hpair hfp in
lemma switched_p : switched σ p q p≠p := by
  intro he
  apply hfp
  have hh : adjusted α p q*switched σ p q=face σ α := by
    simp only [adjusted,switched,face]
    rw [mul_assoc α (Equiv.swap p q),←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
  rw [←hh,Equiv.Perm.mul_apply,he,adjusted_p α hi p q hpair]
omit [Fintype O] in
include hpair hfq in
lemma switched_q : switched σ p q q≠q := by
  intro he
  apply hfq
  have hh : adjusted α p q*switched σ p q=face σ α := by
    simp only [adjusted,switched,face]
    rw [mul_assoc α (Equiv.swap p q),←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
  rw [←hh,Equiv.Perm.mul_apply,he,adjusted_q α p q hpair]
omit [Fintype O] in
include hs in
lemma switched_p_ne_q : switched σ p q p≠q := by
  intro he
  have hh := congrArg (Equiv.swap p q) he
  simp only [switched,Equiv.Perm.mul_apply,Equiv.swap_apply_self,Equiv.swap_apply_right] at hh
  exact hs hh
omit [Fintype O] in
include hs hpair in
lemma face_p_ne_q : face σ α p≠q := by
  intro he
  exact hs (α.injective (he.trans hpair.symm))
include hi hpair hs hfp hfq in
lemma rotation_count : Fintype.card (Cycle (rotation σ p q hpq))=
    Fintype.card (Cycle (switched σ p q)) := by
  rw [rotation,bypass_count]
  · exact bypass_count _ _ (switched_p σ α hi p q hpair hfp)
  · apply bypass_nonfixed
    · exact switched_q σ α p q hpair hfq
    · intro _
      exact switched_p_ne_q σ p q hs
include hs hfp hfq in
lemma face_count : Fintype.card (Cycle (partner α hi p q hpq hpair*rotation σ p q hpq))=
    Fintype.card (Cycle (face σ α)) := by
  rw [face_eq,bypass_count]
  · exact bypass_count _ _ hfp
  · apply bypass_nonfixed
    · exact hfq
    · intro _
      exact face_p_ne_q σ α p q hpair hs
lemma two_fewer : Fintype.card (Residual p q hpq)+2=Fintype.card O := by
  have h₁ := card_rest (p:=p)
  have h₂ := card_rest (p:=q' p q hpq)
  simp only [←Nat.card_eq_fintype_card] at h₁ h₂ ⊢
  change Nat.card (Residual p q hpq)+1=Nat.card (Rest p) at h₂
  omega
include hs hfp hfq in
/-- The literal removal of a paired band preserves the global sphere Euler
lower bound. No componentwise planarity or essentiality is concluded here. -/
theorem euler (he : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (face σ α))) :
    Fintype.card (Residual p q hpq)+4≤2*Fintype.card (Cycle (rotation σ p q hpq))+
      2*Fintype.card (Cycle (partner α hi p q hpq hpair*rotation σ p q hpq)) := by
  rw [rotation_count σ α hi p q hpq hpair hs hfp hfq,face_count σ α hi p q hpq hpair hs hfp hfq]
  have hv := SwapCycles.count_le σ p q
  have hc := two_fewer p q hpq
  change Fintype.card (Cycle σ)≤Fintype.card (Cycle (switched σ p q))+1 at hv
  omega
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
lemma genusZero_fintype {O : Type} (i j : Fintype O) (σ α : Equiv.Perm O) :
    @GenusZero O i σ α ↔ @GenusZero O j σ α := by
  cases Subsingleton.elim i j
  rfl
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
omit [Fintype O] in
include hi hpair in
lemma adjusted_strip : adjusted α p q=PairingFactors.strip α p := by
  rw [←hpair]
  ext x
  change α (Equiv.swap p (α p) x)=Equiv.swap p (α p) (α x)
  rw [←α.injective.swap_apply,hi p,Equiv.swap_comm (α p) p]
include hi hpq hpair in
lemma switched_genusZero (hz : GenusZero σ α) :
    GenusZero (switched σ p q) (adjusted α p q) := by
  rw [adjusted_strip α hi p q hpair]
  have hp : α p≠p := by rw [hpair];exact hpq.symm
  have hh := genusZero_band σ α hi hz p hp
  simpa only [switched,hpair] using hh
include hi hpair in
/-- The genuine remaining map after deleting a paired band has genus zero in
all its actual components. This strengthens the global Euler estimate and uses
no assumed planar embedding. Local degenerate faces are explicitly excluded. -/
theorem genusZero (hz : GenusZero σ α) (hs : σ p≠p)
    (hfp : face σ α p≠p) (hfq : face σ α q≠q) :
    GenusZero (rotation σ p q hpq) (partner α hi p q hpq hpair) := by
  have h₀ := switched_genusZero σ α hi p q hpq hpair hz
  have h₁ := MapDeletion.genusZero_delete (switched σ p q) (adjusted α p q) p
    (adjusted_p α hi p q hpair) (switched_p σ α hi p q hpair hfp) h₀
  have hn : bypass (switched σ p q) p (q' p q hpq)≠q' p q hpq := by
    apply bypass_nonfixed
    · exact switched_q σ α p q hpair hfq
    · intro _
      exact switched_p_ne_q σ p q hs
  have h₂ := MapDeletion.genusZero_delete (bypass (switched σ p q) p) (α₁ α hi p q hpair)
    (q' p q hpq) (α₁_q α hi p q hpq hpair) hn h₁
  exact (genusZero_fintype _ _ _ _).mp h₂
end TorsionFreeZeroDivisors.BandEuler
end
end OAI
