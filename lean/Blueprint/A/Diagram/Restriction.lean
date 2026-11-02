import Blueprint.A.Diagram.Surgery
/-! Generic component restriction port from OpenAI/math, Apache-2.0.
Selected BFSTree.lean lines 350-424 and MapRestrict.lean lines 8-89. -/
namespace OAI
noncomputable section
set_option maxHeartbeats 800000
namespace TorsionFreeZeroDivisors.ConedMap
lemma support_card_nat {X : Type} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :
    p.support.card=Nat.card {x : X // p x≠x} := by
  rw [←Fintype.card_coe,←Nat.card_eq_fintype_card]
  exact Nat.card_congr
    ⟨fun x=>⟨x.val,Equiv.Perm.mem_support.mp x.property⟩,
     fun x=>⟨x.val,Equiv.Perm.mem_support.mpr x.property⟩,
     fun _=>rfl,fun _=>rfl⟩

end TorsionFreeZeroDivisors.ConedMap
namespace TorsionFreeZeroDivisors.MapRestrict
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (P : O→Prop) (hf : ∀ x,P (f x)↔P x)

def perm : Equiv.Perm {x // P x} := f.subtypeEquiv (fun x=>(hf x).symm)
omit [Fintype O] in
@[simp] lemma perm_val (x : {x // P x}) : (perm f P hf x).val=f x := rfl
omit [Fintype O] in
include hf in
lemma not_invariant (x : O) : (¬P (f x))↔¬P x := not_congr (hf x)
local notation "fP" => perm f P hf
local notation "fN" => perm f (fun x=>¬P x) (not_invariant f P hf)

def cycleInclude : Cycle fP→Cycle f :=
  PermutationCycles.lift fP (fun x=>cycle f x.val) (fun x=>cycle_apply f x.val)
@[simp] lemma cycleInclude_cycle (x : {x // P x}) : cycleInclude f P hf (cycle fP x)=cycle f x.val := rfl

def cycleRaw (x : O) : Cycle fP ⊕ Cycle fN :=
  if h:P x then .inl (cycle fP ⟨x,h⟩) else .inr (cycle fN ⟨x,h⟩)
omit [Fintype O] in
lemma cycleRaw_apply (x : O) : cycleRaw f P hf (f x)=cycleRaw f P hf x := by
  by_cases hx : P x
  · rw [cycleRaw,dite_eq_left ((hf x).mpr hx),cycleRaw,dite_eq_left hx]
    exact congrArg Sum.inl (cycle_apply fP ⟨x,hx⟩)
  · rw [cycleRaw,dite_eq_right (fun h=>hx ((hf x).mp h)),cycleRaw,dite_eq_right hx]
    exact congrArg Sum.inr (cycle_apply fN ⟨x,hx⟩)

def cycleEquiv : Cycle f≃Cycle fP ⊕ Cycle fN where
  toFun := PermutationCycles.lift f (cycleRaw f P hf) (cycleRaw_apply f P hf)
  invFun := Sum.elim (cycleInclude f P hf) (cycleInclude f (fun x=>¬P x) (not_invariant f P hf))
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    change (Sum.elim _ _) (cycleRaw f P hf x)=cycle f x
    unfold cycleRaw
    split_ifs <;> rfl
  right_inv := by
    intro c
    rcases c with c|c
    · obtain ⟨x,rfl⟩ := cycle_surjective fP c
      change cycleRaw f P hf x.val=Sum.inl (cycle fP x)
      rw [cycleRaw,dite_eq_left x.property]
    · obtain ⟨x,rfl⟩ := cycle_surjective fN c
      change cycleRaw f P hf x.val=Sum.inr (cycle fN x)
      rw [cycleRaw,dite_eq_right x.property]

lemma cycle_card : Nat.card (Cycle f)=Nat.card (Cycle fP)+Nat.card (Cycle fN) := by
  rw [Nat.card_congr (cycleEquiv f P hf),Nat.card_sum]
omit [Fintype O] in
lemma perm_involutive (hi : Function.Involutive f) : Function.Involutive fP :=
  fun x=>Subtype.ext (hi x.val)

def supportEquiv : {x : O // f x≠x} ≃
    {x : Subtype P // fP x≠x} ⊕ {x : {x // ¬P x} // fN x≠x} where
  toFun x := if h:P x.val then .inl ⟨⟨x.val,h⟩,fun he=>x.property (congrArg Subtype.val he)⟩
    else .inr ⟨⟨x.val,h⟩,fun he=>x.property (congrArg Subtype.val he)⟩
  invFun := Sum.elim (fun x=>⟨x.val.val,fun he=>x.property (Subtype.ext he)⟩)
    (fun x=>⟨x.val.val,fun he=>x.property (Subtype.ext he)⟩)
  left_inv := by intro x;dsimp;split_ifs <;> rfl
  right_inv := by
    intro x
    rcases x with x|x
    · dsimp
      rw [dite_eq_left x.val.property]
    · dsimp
      rw [dite_eq_right x.val.property]

lemma support_card : f.support.card=(fP).support.card+(fN).support.card := by
  simp only [ConedMap.support_card_nat]
  rw [Nat.card_congr (supportEquiv f P hf),Nat.card_sum]

end TorsionFreeZeroDivisors.MapRestrict

namespace TorsionFreeZeroDivisors.MapRestrict

section
open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (P : O→Prop)
    (hs : ∀ x,P (σ x)↔P x) (ha : ∀ x,P (α x)↔P x)
local notation "σP" => perm σ P hs
local notation "αP" => perm α P ha
local notation "σN" => perm σ (fun x=>¬P x) (not_invariant σ P hs)
local notation "αN" => perm α (fun x=>¬P x) (not_invariant α P ha)

def componentInclude : Component σP αP→ Component σ α :=
  MapEuler.lift σP αP (fun x=>component σ α x.val)
    (fun x=>component_rotation σ α x.val) (fun x=>component_partner σ α x.val)
omit [Fintype O] in
@[simp] lemma componentInclude_component (x : Subtype P) :
    componentInclude σ α P hs ha (component σP αP x)=component σ α x.val := rfl

def componentRaw (x : O) : Component σP αP ⊕ Component σN αN :=
  if h:P x then .inl (component σP αP ⟨x,h⟩) else .inr (component σN αN ⟨x,h⟩)
omit [Fintype O] in
lemma componentRaw_rotation (x : O) : componentRaw σ α P hs ha (σ x)=componentRaw σ α P hs ha x := by
  by_cases hx : P x
  · rw [componentRaw,dite_eq_left ((hs x).mpr hx),componentRaw,dite_eq_left hx]
    exact congrArg Sum.inl (component_rotation σP αP ⟨x,hx⟩)
  · rw [componentRaw,dite_eq_right (fun h=>hx ((hs x).mp h)),componentRaw,dite_eq_right hx]
    exact congrArg Sum.inr (component_rotation σN αN ⟨x,hx⟩)
omit [Fintype O] in
lemma componentRaw_partner (x : O) : componentRaw σ α P hs ha (α x)=componentRaw σ α P hs ha x := by
  by_cases hx : P x
  · rw [componentRaw,dite_eq_left ((ha x).mpr hx),componentRaw,dite_eq_left hx]
    exact congrArg Sum.inl (component_partner σP αP ⟨x,hx⟩)
  · rw [componentRaw,dite_eq_right (fun h=>hx ((ha x).mp h)),componentRaw,dite_eq_right hx]
    exact congrArg Sum.inr (component_partner σN αN ⟨x,hx⟩)

def componentEquiv : Component σ α≃Component σP αP ⊕ Component σN αN where
  toFun := MapEuler.lift σ α (componentRaw σ α P hs ha)
    (componentRaw_rotation σ α P hs ha) (componentRaw_partner σ α P hs ha)
  invFun := Sum.elim (componentInclude σ α P hs ha)
    (componentInclude σ α (fun x=>¬P x) (not_invariant σ P hs) (not_invariant α P ha))
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change (Sum.elim _ _) (componentRaw σ α P hs ha x)=component σ α x
    unfold componentRaw
    split_ifs <;> rfl
  right_inv := by
    intro c
    rcases c with c|c
    · obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
      change componentRaw σ α P hs ha x.val=Sum.inl (component σP αP x)
      rw [componentRaw,dite_eq_left x.property]
    · obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
      change componentRaw σ α P hs ha x.val=Sum.inr (component σN αN x)
      rw [componentRaw,dite_eq_right x.property]

lemma component_card : Nat.card (Component σ α)=Nat.card (Component σP αP)+Nat.card (Component σN αN) := by
  rw [Nat.card_congr (componentEquiv σ α P hs ha),Nat.card_sum]

omit [Fintype O] in
include hs ha in
lemma mul_invariant (x : O) : P ((α*σ) x)↔P x := (ha (σ x)).trans (hs x)
omit [Fintype O] in
lemma perm_mul : perm (α*σ) P (mul_invariant σ α P hs ha)=αP*σP := rfl

/-- Restriction to any invariant union of map components preserves actual
Euler genus zero. The proof uses decomposition and the universal Euler upper
bound on BOTH complementary pieces. -/
theorem genusZero (hi : Function.Involutive α) (hz : GenusZero σ α) : GenusZero σP αP := by
  have hs' := cycle_card σ P hs
  have hf' := cycle_card (α*σ) P (mul_invariant σ α P hs ha)
  have ha' := support_card α P ha
  have hc' := component_card σ α P hs ha
  have hP := MapEuler.upper σP αP (perm_involutive α P ha hi)
  have hN := MapEuler.upper σN αN (perm_involutive α (fun x=>¬P x) (not_invariant α P ha) hi)
  have heN : perm (α*σ) (fun x=>¬P x) (not_invariant (α*σ) P (mul_invariant σ α P hs ha))=αN*σN := rfl
  rw [perm_mul σ α P hs ha,heN] at hf'
  unfold GenusZero at hz ⊢
  simp only [ConedMap.support_card_nat] at ha' hP hN hz ⊢
  omega

end
end TorsionFreeZeroDivisors.MapRestrict
end
end OAI
