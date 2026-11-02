import Blueprint.A.Diagram.Pairing

/-! Proof port from OpenAI/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-APACHE-2.0-OpenAI and PROVENANCE.json.
Modified: selected generic namespaces, narrowed imports, split modules for Lean 4.35.0. -/

namespace OAI
noncomputable section
set_option maxHeartbeats 800000

namespace TorsionFreeZeroDivisors.BoundarySurgery
open scoped Classical
open DeleteCycle BandEuler
variable {O V : Type} [Fintype O] (σ : Equiv.Perm O) (before after : O→V)
/-- Consecutive edge endpoint agreement. A marked exterior break can be encoded
by one extra formal item with distinct prescribed before/after endpoints. -/
def Consistent : Prop := ∀ x,after x=before (σ x)
include σ in
lemma bypass_consistent (h : Consistent σ before after) (p : O) (hp : after p=before p) :
    Consistent (bypass σ p) (fun x : Rest p=>before x) (fun x : Rest p=>after x) := by
  intro x
  change after (x : O)=before ((bypass σ p x : Rest p) : O)
  rw [bypass_apply,MapEuler.swap_invariant before p (σ p) (hp.symm.trans (h p))]
  exact h x
variable (p q : O) (hpq : p≠q)
def swappedBefore (x : O) : V := before (Equiv.swap p q x)
omit [Fintype O] in
lemma switched_consistent (h : Consistent σ before after) :
    Consistent (switched σ p q) (swappedBefore before p q) after := by
  intro x
  change after x=before (Equiv.swap p q (Equiv.swap p q (σ x)))
  rw [Equiv.swap_apply_self]
  exact h x
/-- The literal band-spliced boundary preserves the graph endpoint equations.
The two crossed endpoints are exactly those forced by an edge and its reverse.
No statement about homotopy or essentiality is hidden in this combinatorial
lemma, and neither distinct-boundary nor same-boundary cases are excluded. -/
theorem consistent (h : Consistent σ before after)
    (hp : after p=before q) (hq : after q=before p) :
    Consistent (rotation σ p q hpq) (fun x=>before (val p q hpq x))
      (fun x=>after (val p q hpq x)) := by
  have hp' : after p=swappedBefore before p q p := by rw [swappedBefore,Equiv.swap_apply_left];exact hp
  have hq' : after q=swappedBefore before p q q := by rw [swappedBefore,Equiv.swap_apply_right];exact hq
  have h₁ := bypass_consistent (switched σ p q) (swappedBefore before p q) after
    (switched_consistent σ before after p q h) p hp'
  have h₂ := bypass_consistent (bypass (switched σ p q) p)
    (fun x : Rest p=>swappedBefore before p q x) (fun x : Rest p=>after x) h₁
    (q' p q hpq) hq'
  intro x
  have hh := h₂ x
  change after (val p q hpq x)=swappedBefore before p q (val p q hpq (rotation σ p q hpq x)) at hh
  rw [swappedBefore,Equiv.swap_apply_of_ne_of_ne (val_ne_p p q hpq _) (val_ne_q p q hpq _)] at hh
  exact hh
/-- A surviving exterior marker keeps its prescribed distinct endpoints, so
its new boundary contains at least one actual edge after the deletion. -/
lemma marker_nonfixed (h : Consistent σ before after)
    (hp : after p=before q) (hq : after q=before p)
    (m : Residual p q hpq) (hm : after (val p q hpq m)≠before (val p q hpq m)) :
    rotation σ p q hpq m≠m := by
  intro he
  have hh := consistent σ before after p q hpq h hp hq m
  rw [he] at hh
  exact hm hh
end TorsionFreeZeroDivisors.BoundarySurgery

namespace TorsionFreeZeroDivisors.VertexSplit
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
  (l : List (O×O)) (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
  (he : ∀e∈l,α e.1=e.2)
  (hc : cycle σ p=cycle σ q)
local notation "σ'" => Equiv.swap p q*σ
local notation "L'" => (α p,α q)::l
local notation "f'" => forest σ' L'
include hl in
lemma forest_partner (x : O) : cycle f' (α x)=cycle f' x := by
  have h := MapEuler.product_invariant l (cycle f')
    (fun e h=>forest_pair σ' L' e (List.mem_cons_of_mem _ h)) x
  simpa only [hl] using h
include hl in
lemma forest_join : cycle f' p=cycle f' q := by
  have h := forest_pair σ' L' (α p,α q) List.mem_cons_self
  dsimp only at h
  rw [forest_partner σ α p q l hl,forest_partner σ α p q l hl] at h
  exact h
include hl in
lemma forest_rotation (x : O) : cycle f' (σ x)=cycle f' x := by
  have hh := forest_refines σ' L' (σ' x) x (cycle_apply σ' x)
  change cycle f' (Equiv.swap p q (σ x))=cycle f' x at hh
  rw [SwapCycles.cycle_swap f' p q (forest_join σ α p q l hl) (σ x)] at hh
  exact hh
include he hc in
lemma original_invariant (x : O) : MapEuler.component σ α (f' x)=MapEuler.component σ α x := by
  have hpq : MapEuler.component σ α p=MapEuler.component σ α q :=
    MapEuler.component_sameCycle σ α ((cycle_eq σ).mp hc)
  apply invariant_forest σ' L' (MapEuler.component σ α)
  · intro y
    change MapEuler.component σ α (Equiv.swap p q (σ y))=MapEuler.component σ α y
    rw [MapEuler.swap_invariant (MapEuler.component σ α) p q hpq]
    exact MapEuler.component_rotation σ α y
  · intro e h
    rcases List.mem_cons.mp h with rfl|h
    · dsimp only
      rw [MapEuler.component_partner,MapEuler.component_partner]
      exact hpq
    · rw [←he e h]
      exact (MapEuler.component_partner σ α e.1).symm

def toOriginal : Cycle f' → MapEuler.Component σ α :=
  PermutationCycles.lift f' (MapEuler.component σ α) (original_invariant σ α p q l he hc)
def toForest : MapEuler.Component σ α → Cycle f' :=
  MapEuler.lift σ α (cycle f') (forest_rotation σ α p q l hl) (forest_partner σ α p q l hl)
def componentEquiv : Cycle f' ≃ MapEuler.Component σ α :=
  Equiv.ofBijective (toOriginal σ α p q l he hc) ⟨by
    intro c d h
    obtain ⟨x,rfl⟩ := cycle_surjective f' c
    obtain ⟨y,rfl⟩ := cycle_surjective f' d
    exact congrArg (toForest σ α p q l hl) h,
    PermutationCycles.lift_surjective _ _ _ Quotient.mk_surjective⟩
omit [Fintype O] in
include hl in
lemma face_eq : face σ' L'=α*σ := by
  rw [MapEuler.face_product,List.map_cons,List.prod_cons,hl]
  have hs : Equiv.swap (α p) (α q)*α=α*Equiv.swap p q := by
    ext x
    exact α.injective.swap_apply p q x
  rw [hs,mul_assoc,←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
include hi in
/-- Splitting a vertex along two gaps preserves combinatorial genus zero.
This permits empty/isolated components and needs no topological embedding
assumption. The two gaps must be on the same actual vertex cycle. -/
theorem genusZero_vertexSplit (hz : GenusZero σ α) (p q : O) (hpq : p≠q)
    (hc : cycle σ p=cycle σ q) : GenusZero (Equiv.swap p q*σ) α := by
  obtain ⟨l,hl,hL,he⟩ := PairingFactors.factorization α hi
  let σ' := Equiv.swap p q*σ
  let L' := (α p,α q)::l
  have hC := Nat.card_congr (VertexSplit.componentEquiv σ α p q l hl (fun e h=>(he e h).2) hc)
  have hV := SwapCycles.split_count σ p q hpq hc
  simp only [←Nat.card_eq_fintype_card] at hV
  have hF := VertexSplit.face_eq σ α p q l hl
  have hD : ∀e∈L',e.1≠e.2 := by
    intro e h
    rcases List.mem_cons.mp h with rfl|h
    · exact fun h=>hpq (α.injective h)
    · exact (he e h).1
  have hh := handles_exact σ' L' hD
  change Nat.card (Cycle σ')+Nat.card (Cycle (face σ' L'))+2*handles σ' L'=
    L'.length+2*Nat.card (Cycle (forest σ' L')) at hh
  change face σ' L'=α*σ at hF
  rw [hF,hC] at hh
  have hh₀ : handles σ' L'=0 := by
    dsimp only [L',List.length_cons] at hh
    dsimp only [GenusZero] at hz
    change Nat.card (Cycle σ')=Nat.card (Cycle σ)+1 at hV
    change handles σ' ((α p,α q)::l)=0
    omega
  have ht : handles σ' l=0 := Nat.eq_zero_of_le_zero
    ((handles_tail σ' (α p,α q) l).trans_eq hh₀)
  exact (genusZero_iff_handles σ' α l hl he hL).mpr ht
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapConjugation
open scoped Classical
open MapEuler PermutationCycles
variable {A B : Type} (e : A ≃ B) (σ α : Equiv.Perm A)
local notation "σ'" => e.permCongr σ
local notation "α'" => e.permCongr α
def forward : Component σ α → Component σ' α' :=
  MapEuler.lift σ α (fun x=>component σ' α' (e x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_rotation σ' α' (e x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_partner σ' α' (e x))
def backward : Component σ' α' → Component σ α :=
  MapEuler.lift σ' α' (fun x=>component σ α (e.symm x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_rotation σ α (e.symm x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_partner σ α (e.symm x))
def components : Component σ α ≃ Component σ' α' where
  toFun := forward e σ α
  invFun := backward e σ α
  left_inv c := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change component σ α (e.symm (e x))=component σ α x
    rw [e.symm_apply_apply]
  right_inv c := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change component σ' α' (e (e.symm x))=component σ' α' x
    rw [e.apply_symm_apply]
variable [Fintype A] [Fintype B]
def supports : ↥α.support ≃ ↥(α').support where
  toFun x := ⟨e x,by
    apply Equiv.Perm.mem_support.mpr
    intro h
    have hn := Equiv.Perm.mem_support.mp x.property
    exact hn (e.injective (by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using h))⟩
  invFun x := ⟨e.symm x,by
    apply Equiv.Perm.mem_support.mpr
    intro h
    have hn := Equiv.Perm.mem_support.mp x.property
    apply hn
    change e (α (e.symm x))=x
    rw [h,e.apply_symm_apply]⟩
  left_inv x := by ext;simp
  right_inv x := by ext;simp
lemma support_count : (α').support.card=α.support.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (supports e α)).symm
/-- Changing the actual finite occurrence coordinates does not change genus. -/
theorem genusZero (h : GenusZero σ α) : GenusZero σ' α' := by
  have hC := Nat.card_congr (components e σ α)
  have hV := Nat.card_congr (PermutationTransport.cycles e σ)
  have hF := Nat.card_congr (PermutationTransport.cycles e (α*σ))
  rw [PermutationTransport.mul] at hF
  have hE := support_count e α
  dsimp only [GenusZero] at h ⊢
  rw [←hC,←hV,←hF,hE]
  exact h
end TorsionFreeZeroDivisors.MapConjugation

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.MatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (hf : ∀x,α x≠x) (p q : O) (hpq : p≠q)

abbrev Remaining := {x : O // x≠p ∧ x≠q}
def splice (x : O) : O := if α x=p then α q else if α x=q then α p else α x

include hi hf in
lemma splice_avoids (x : Remaining p q) : splice α p q x≠p ∧ splice α p q x≠q := by
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hqp : α q≠p := by
      intro h
      have h' : q=α p := (hi _).symm.trans (congrArg α h)
      exact x.property.2 (hx ▸ h'.symm)
    rw [splice,ite_eq_left h1]
    exact ⟨hqp,hf q⟩
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hpq' : α p≠q := by
        intro h
        have h' : p=α q := (hi _).symm.trans (congrArg α h)
        exact x.property.1 (hx ▸ h'.symm)
      rw [splice,ite_eq_right h1,ite_eq_left h2]
      exact ⟨hf p,hpq'⟩
    · rw [splice,ite_eq_right h1,ite_eq_right h2]
      exact ⟨h1,h2⟩

def apply (x : Remaining p q) : Remaining p q := ⟨splice α p q x,splice_avoids α hi hf p q x⟩

include hpq in
lemma involutive : Function.Involutive (apply α hi hf p q) := by
  intro x
  apply Subtype.ext
  change splice α p q (splice α p q x)=x
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hs : splice α p q x=α q := by rw [splice,ite_eq_left h1]
    rw [hs,splice,hi q,ite_eq_right hpq.symm,ite_eq_left rfl]
    exact hx
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hs : splice α p q x=α p := by rw [splice,ite_eq_right h1,ite_eq_left h2]
      rw [hs,splice,hi p,ite_eq_left rfl]
      exact hx
    · have hs : splice α p q x=α x := by rw [splice,ite_eq_right h1,ite_eq_right h2]
      rw [hs,splice,hi x,ite_eq_right x.property.1,ite_eq_right x.property.2]

include hpq in
lemma distinct (x : Remaining p q) : apply α hi hf p q x≠x := by
  intro he
  have he := congrArg Subtype.val he
  change splice α p q x=x at he
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    rw [splice,ite_eq_left h1] at he
    exact hpq (α.injective (hx.trans he.symm))
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      rw [splice,ite_eq_right h1,ite_eq_left h2] at he
      exact hpq (α.injective (he.trans hx.symm))
    · exact hf x (by simpa [splice,h1,h2] using he)

def partner : Equiv.Perm (Remaining p q) := ⟨apply α hi hf p q,apply α hi hf p q,involutive α hi hf p q hpq,involutive α hi hf p q hpq⟩

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))
include hinv hl hlabel in
lemma compatible (x : Remaining p q) :
    label (partner α hi hf p q hpq x)=inv (label x) := by
  change label (splice α p q x)=_
  by_cases h1 : α x=p
  · rw [splice,ite_eq_left h1,hl,hlabel,hinv]
    exact (congrArg label h1).symm.trans (hl x)
  · by_cases h2 : α x=q
    · rw [splice,ite_eq_right h1,ite_eq_left h2,hl,←hlabel]
      exact (congrArg label h2).symm.trans (hl x)
    · rw [splice,ite_eq_right h1,ite_eq_right h2,hl]

end TorsionFreeZeroDivisors.MatchingSurgery
namespace TorsionFreeZeroDivisors.Smoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (hf : ∀x,α x≠x)
  (p q : O) (hpq : p≠q) (hsp : σ p=q) (hsq : σ q=p)

include hsp hsq in
lemma rotation_invariant (x : O) : (σ x≠p ∧ σ x≠q) ↔ (x≠p ∧ x≠q) := by
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (h ▸ hsp),fun h=>hp (h ▸ hsq)⟩
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (σ.injective (h.trans hsq.symm)),fun h=>hp (σ.injective (h.trans hsp.symm))⟩
def rotation : Equiv.Perm (MatchingSurgery.Remaining p q) :=
  σ.subtypePerm (rotation_invariant σ p q hsp hsq)

abbrev r := α p
include hf in
lemma pr : p≠r α p := (hf p).symm
include hf hpq in
lemma rename_invariant (x : O) :
    (Equiv.swap q (r α p) x≠p ∧ Equiv.swap q (r α p) x≠q) ↔ (x≠p ∧ x≠r α p) := by
  have hp : Equiv.swap q (r α p) p=p := Equiv.swap_apply_of_ne_of_ne hpq (pr α hf p)
  have hr : Equiv.swap q (r α p) (r α p)=q := Equiv.swap_apply_right _ _
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 (h ▸ hp),fun h=>h2 (h ▸ hr)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 ((Equiv.swap q (r α p)).injective (h.trans hp.symm)),
      fun h=>h2 ((Equiv.swap q (r α p)).injective (h.trans hr.symm))⟩
def flatten : BandEuler.Residual p (r α p) (pr α hf p) ≃ MatchingSurgery.Remaining p (r α p) where
  toFun x := ⟨BandEuler.val p (r α p) (pr α hf p) x,
    BandEuler.val_ne_p p (r α p) (pr α hf p) x,BandEuler.val_ne_q p (r α p) (pr α hf p) x⟩
  invFun x := ⟨⟨x,x.property.1⟩,fun he=>x.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def rename : MatchingSurgery.Remaining p (r α p) ≃ MatchingSurgery.Remaining p q :=
  (Equiv.swap q (r α p)).subtypeEquiv (fun x=>(rename_invariant α hf p q hpq x).symm)
def coordinates : BandEuler.Residual p (r α p) (pr α hf p) ≃ MatchingSurgery.Remaining p q :=
  (flatten α hf p).trans (rename α hf p q hpq)
lemma coordinates_val (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    (coordinates α hf p q hpq x).val=Equiv.swap q (r α p) (BandEuler.val p (r α p) (pr α hf p) x) := rfl

lemma partner_commutes (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    coordinates α hf p q hpq (BandEuler.partner α hi p (r α p) (pr α hf p) rfl x)=
      MatchingSurgery.partner α hi hf p q hpq (coordinates α hf p q hpq x) := by
  apply Subtype.ext
  rw [coordinates_val,BandEuler.partner_val]
  change Equiv.swap q (α p) (α (BandEuler.val p (α p) (pr α hf p) x))=
    MatchingSurgery.splice α p q (Equiv.swap q (α p) (BandEuler.val p (α p) (pr α hf p) x))
  let v := BandEuler.val p (α p) (pr α hf p) x
  change Equiv.swap q (α p) (α v)=MatchingSurgery.splice α p q (Equiv.swap q (α p) v)
  have hvp : v≠p := BandEuler.val_ne_p _ _ _ x
  have hvr : v≠α p := BandEuler.val_ne_q _ _ _ x
  have havp : α v≠p := fun h=>hvr ((hi _).symm.trans (congrArg α h))
  have havr : α v≠α p := α.injective.ne hvp
  by_cases hvq : v=q
  · rw [hvq,Equiv.swap_apply_left,MatchingSurgery.splice,hi p,ite_eq_left rfl]
    have hαq : α q≠q := hf q
    have hαqr : α q≠α p := α.injective.ne hpq.symm
    exact Equiv.swap_apply_of_ne_of_ne hαq hαqr
  · rw [Equiv.swap_apply_of_ne_of_ne hvq hvr,MatchingSurgery.splice,ite_eq_right havp]
    by_cases havq : α v=q
    · rw [ite_eq_left havq,havq,Equiv.swap_apply_left]
    · rw [ite_eq_right havq,Equiv.swap_apply_of_ne_of_ne havq havr]

lemma bypass_value (f : Equiv.Perm O) (a : O) (x : Rest a) :
    (bypass f a x).val=if f x=a then f a else f x := by
  change Equiv.swap a (f a) (f x)=_
  by_cases h : f x=a
  · rw [ite_eq_left h,h,Equiv.swap_apply_left]
  · rw [ite_eq_right h,Equiv.swap_apply_of_ne_of_ne h (f.injective.ne x.property)]
lemma rotation_value (a b : O) (hab : a≠b) (x : BandEuler.Residual a b hab) :
    BandEuler.val a b hab (BandEuler.rotation σ a b hab x)=
      let f := BandEuler.switched σ a b
      let g := fun y=>if f y=a then f a else f y
      if g (BandEuler.val a b hab x)=b then g b else g (BandEuler.val a b hab x) := by
  let f := BandEuler.switched σ a b
  let g := fun y=>if f y=a then f a else f y
  change ((bypass (bypass f a) (BandEuler.q' a b hab) x).val).val=
    if g x.val.val=b then g b else g x.val.val
  have he : bypass f a x.val=BandEuler.q' a b hab ↔ g x.val.val=b := by
    rw [Subtype.ext_iff,bypass_value]
  by_cases hc : g x.val.val=b
  · rw [ite_eq_left hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_left (he.mpr hc)] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a (BandEuler.q' a b hab))
  · rw [ite_eq_right hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_right (fun h=>hc (he.mp h))] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a x.val)

include hsp hsq hpq in
lemma smoothing_value (r v : O) (hpr : p≠r) (hvp : v≠p) (hvr : v≠r) :
    let f := Equiv.swap p r*σ
    let g := fun y=>if f y=p then f p else f y
    Equiv.swap q r (if g v=r then g r else g v)=σ (Equiv.swap q r v) := by
  let f := Equiv.swap p r*σ
  let g := fun y=>if f y=p then f p else f y
  change Equiv.swap q r (if g v=r then g r else g v)=_
  by_cases hqr : q=r
  · subst r
    have hsvp : σ v≠p := fun h=>hvr (σ.injective (h.trans hsq.symm))
    have hsvq : σ v≠q := fun h=>hvp (σ.injective (h.trans hsp.symm))
    have hfv : f v=σ v := Equiv.swap_apply_of_ne_of_ne hsvp hsvq
    have hg : g v=σ v := by
      change (if f v=p then f p else f v)=σ v
      simp only [hfv,ite_eq_right hsvp]
    rw [hg,ite_eq_right hsvq,Equiv.swap_self]
    rfl
  · have hfp : f p=q := by
      dsimp only [f,Equiv.Perm.mul_apply]
      rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm hqr]
    have hG (y : O) (hyp : y≠p) (hyq : y≠q) : Equiv.swap q r (g y)=σ y := by
      have hsyp : σ y≠p := fun h=>hyq (σ.injective (h.trans hsq.symm))
      have hsyq : σ y≠q := fun h=>hyp (σ.injective (h.trans hsp.symm))
      by_cases hsyr : σ y=r
      · have hfy : f y=p := by simp only [f,Equiv.Perm.mul_apply,hsyr,Equiv.swap_apply_right]
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        rw [ite_eq_left hfy,hfp,Equiv.swap_apply_left,hsyr]
      · have hfy : f y=σ y := by
          exact Equiv.swap_apply_of_ne_of_ne hsyp hsyr
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        simp only [hfy,ite_eq_right hsyp,Equiv.swap_apply_of_ne_of_ne hsyq hsyr]
    by_cases hvq : v=q
    · have hfq : f q=r := by simp only [f,Equiv.Perm.mul_apply,hsq,Equiv.swap_apply_left]
      have hgq : g q=r := by
        change (if f q=p then f p else f q)=r
        simp only [hfq,ite_eq_right hpr.symm]
      rw [hvq,hgq,ite_eq_left rfl,Equiv.swap_apply_left]
      exact hG r hpr.symm (Ne.symm hqr)
    · have hgv : g v≠r := by
        intro he
        have hh := hG v hvp hvq
        rw [he,Equiv.swap_apply_right] at hh
        exact hvp (σ.injective (hh.symm.trans hsp.symm))
      rw [ite_eq_right hgv,Equiv.swap_apply_of_ne_of_ne hvq hvr]
      exact hG v hvp hvq

lemma rotation_commutes (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    coordinates α hf p q hpq (BandEuler.rotation σ p (r α p) (pr α hf p) x)=
      rotation σ p q hsp hsq (coordinates α hf p q hpq x) := by
  apply Subtype.ext
  rw [coordinates_val,rotation_value]
  exact smoothing_value σ p q hpq hsp hsq (r α p)
    (BandEuler.val p (r α p) (pr α hf p) x) (pr α hf p)
    (BandEuler.val_ne_p _ _ _ x) (BandEuler.val_ne_q _ _ _ x)

variable [Fintype O]
/-- Suppressing an actual two-occurrence boundary splices its matching partners,
including the already-paired case, and preserves combinatorial genus zero. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hsp hsq)
      (MatchingSurgery.partner α hi hf p q hpq) := by
  let e := coordinates α hf p q hpq
  let σ₀ := BandEuler.rotation σ p (r α p) (pr α hf p)
  let α₀ := BandEuler.partner α hi p (r α p) (pr α hf p) rfl
  have hz₀ : MapEuler.GenusZero σ₀ α₀ := BandEuler.genusZero_all σ α hi p
    (r α p) (pr α hf p) rfl hz
  have h := MapConjugation.genusZero e σ₀ α₀ hz₀
  have hσ : e.permCongr σ₀=rotation σ p q hsp hsq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact rotation_commutes σ α hf p q hpq hsp hsq x
  have hα : e.permCongr α₀=MatchingSurgery.partner α hi hf p q hpq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact partner_commutes α hi hf p q hpq x
  rwa [hσ,hα] at h

end TorsionFreeZeroDivisors.Smoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
open PermutationCycles
variable {O V : Type} (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
def isolate : Equiv.Perm O := Equiv.swap p (σ q)*σ
include hpq hsp in
lemma q_ne_next : q≠σ q := fun h=>hpq (σ.injective (hsp.trans h))
include hpq hsp in
lemma isolate_p : isolate σ p q p=q := by
  change Equiv.swap p (σ q) (σ p)=q
  rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm (q_ne_next σ p q hpq hsp)]
lemma isolate_q : isolate σ p q q=p := Equiv.swap_apply_right _ _
def rotation : Equiv.Perm (MatchingSurgery.Remaining p q) :=
  Smoothing.rotation (isolate σ p q) p q (isolate_p σ p q hpq hsp) (isolate_q σ p q)

variable [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀x,α x≠x)
include hsp hi in
lemma isolate_genusZero (hz : MapEuler.GenusZero σ α) : MapEuler.GenusZero (isolate σ p q) α := by
  by_cases he : p=σ q
  · have hs : isolate σ p q=σ := by rw [isolate,←he,Equiv.swap_self];rfl
    rwa [hs]
  · apply MapEuler.genusZero_vertexSplit σ α hi hz p (σ q) he
    rw [cycle_apply,←hsp,cycle_apply]
/-- Deleting an actual adjacent backtracking pair from its boundary, with the
forced partner splice, preserves genus zero even if the two occurrences were
not paired. This supplies the finite-map part of cyclic tightening. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hpq hsp) (MatchingSurgery.partner α hi hf p q hpq) :=
  Smoothing.genusZero (isolate σ p q) α hi hf p q hpq
    (isolate_p σ p q hpq hsp) (isolate_q σ p q) (isolate_genusZero σ p q hsp α hi hz)

variable (before after : O→V)
omit [Fintype O] in
/-- The graph endpoint conditions, not just the rose labels, survive the
backtracking deletion. The second occurrence really returns to the first
occurrence's starting vertex. -/
theorem consistent (h : BoundarySurgery.Consistent σ before after) (hq : after q=before p) :
    BoundarySurgery.Consistent (rotation σ p q hpq hsp)
      (fun x=>before x) (fun x=>after x) := by
  have he : before p=before (σ q) := hq.symm.trans (h q)
  intro x
  change after (x : O)=before (Equiv.swap p (σ q) (σ x))
  rw [MapEuler.swap_invariant before p (σ q) he]
  exact h x
omit [Fintype O] in
lemma marker_nonfixed (h : BoundarySurgery.Consistent σ before after) (hq : after q=before p)
    (m : MatchingSurgery.Remaining p q) (hm : after m≠before m) :
    rotation σ p q hpq hsp m≠m := by
  intro he
  have hh := consistent σ p q hpq hsp before after h hq m
  rw [he] at hh
  exact hm hh
end TorsionFreeZeroDivisors.Tightening

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.PartialMatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q)

abbrev Remaining := {x : O // x≠p ∧ x≠q}
def splice (x : O) : O := if α x=p then α q else if α x=q then α p else α x

include hi hfp hfq in
lemma splice_avoids (x : Remaining p q) : splice α p q x≠p ∧ splice α p q x≠q := by
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hqp : α q≠p := by
      intro h
      have h' : q=α p := (hi _).symm.trans (congrArg α h)
      exact x.property.2 (hx ▸ h'.symm)
    rw [splice,ite_eq_left h1]
    exact ⟨hqp,hfq⟩
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hpq' : α p≠q := by
        intro h
        have h' : p=α q := (hi _).symm.trans (congrArg α h)
        exact x.property.1 (hx ▸ h'.symm)
      rw [splice,ite_eq_right h1,ite_eq_left h2]
      exact ⟨hfp,hpq'⟩
    · rw [splice,ite_eq_right h1,ite_eq_right h2]
      exact ⟨h1,h2⟩

def apply (x : Remaining p q) : Remaining p q := ⟨splice α p q x,splice_avoids α hi p q hfp hfq x⟩

include hpq in
lemma involutive : Function.Involutive (apply α hi p q hfp hfq) := by
  intro x
  apply Subtype.ext
  change splice α p q (splice α p q x)=x
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hs : splice α p q x=α q := by rw [splice,ite_eq_left h1]
    rw [hs,splice,hi q,ite_eq_right hpq.symm,ite_eq_left rfl]
    exact hx
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hs : splice α p q x=α p := by rw [splice,ite_eq_right h1,ite_eq_left h2]
      rw [hs,splice,hi p,ite_eq_left rfl]
      exact hx
    · have hs : splice α p q x=α x := by rw [splice,ite_eq_right h1,ite_eq_right h2]
      rw [hs,splice,hi x,ite_eq_right x.property.1,ite_eq_right x.property.2]

include hpq in
lemma distinct (x : Remaining p q) (hfx : α x≠x) : apply α hi p q hfp hfq x≠x := by
  intro he
  have he := congrArg Subtype.val he
  change splice α p q x=x at he
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    rw [splice,ite_eq_left h1] at he
    exact hpq (α.injective (hx.trans he.symm))
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      rw [splice,ite_eq_right h1,ite_eq_left h2] at he
      exact hpq (α.injective (he.trans hx.symm))
    · exact hfx (by simpa [splice,h1,h2] using he)

def partner : Equiv.Perm (Remaining p q) := ⟨apply α hi p q hfp hfq,apply α hi p q hfp hfq,involutive α hi p q hpq hfp hfq,involutive α hi p q hpq hfp hfq⟩

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))
include hinv hl hlabel in
lemma compatible (x : Remaining p q) :
    label (partner α hi p q hpq hfp hfq x)=inv (label x) := by
  change label (splice α p q x)=_
  by_cases h1 : α x=p
  · rw [splice,ite_eq_left h1,hl,hlabel,hinv]
    exact (congrArg label h1).symm.trans (hl x)
  · by_cases h2 : α x=q
    · rw [splice,ite_eq_right h1,ite_eq_left h2,hl,←hlabel]
      exact (congrArg label h2).symm.trans (hl x)
    · rw [splice,ite_eq_right h1,ite_eq_right h2,hl]

lemma fixed (x : Remaining p q) (hx : α x=x) : partner α hi p q hpq hfp hfq x=x := by
  apply Subtype.ext
  change splice α p q x=x
  rw [splice,hx,ite_eq_right x.property.1,ite_eq_right x.property.2]

end TorsionFreeZeroDivisors.PartialMatchingSurgery
namespace TorsionFreeZeroDivisors.PartialSmoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q) (hsp : σ p=q) (hsq : σ q=p)

include hsp hsq in
lemma rotation_invariant (x : O) : (σ x≠p ∧ σ x≠q) ↔ (x≠p ∧ x≠q) := by
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (h ▸ hsp),fun h=>hp (h ▸ hsq)⟩
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (σ.injective (h.trans hsq.symm)),fun h=>hp (σ.injective (h.trans hsp.symm))⟩
def rotation : Equiv.Perm (PartialMatchingSurgery.Remaining p q) :=
  σ.subtypePerm (rotation_invariant σ p q hsp hsq)

abbrev r := α p
include hfp in
lemma pr : p≠r α p := (hfp).symm
include hfp hpq in
lemma rename_invariant (x : O) :
    (Equiv.swap q (r α p) x≠p ∧ Equiv.swap q (r α p) x≠q) ↔ (x≠p ∧ x≠r α p) := by
  have hp : Equiv.swap q (r α p) p=p := Equiv.swap_apply_of_ne_of_ne hpq (pr α p hfp)
  have hr : Equiv.swap q (r α p) (r α p)=q := Equiv.swap_apply_right _ _
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 (h ▸ hp),fun h=>h2 (h ▸ hr)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 ((Equiv.swap q (r α p)).injective (h.trans hp.symm)),
      fun h=>h2 ((Equiv.swap q (r α p)).injective (h.trans hr.symm))⟩
def flatten : BandEuler.Residual p (r α p) (pr α p hfp) ≃ PartialMatchingSurgery.Remaining p (r α p) where
  toFun x := ⟨BandEuler.val p (r α p) (pr α p hfp) x,
    BandEuler.val_ne_p p (r α p) (pr α p hfp) x,BandEuler.val_ne_q p (r α p) (pr α p hfp) x⟩
  invFun x := ⟨⟨x,x.property.1⟩,fun he=>x.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def rename : PartialMatchingSurgery.Remaining p (r α p) ≃ PartialMatchingSurgery.Remaining p q :=
  (Equiv.swap q (r α p)).subtypeEquiv (fun x=>(rename_invariant α p q hpq hfp x).symm)
def coordinates : BandEuler.Residual p (r α p) (pr α p hfp) ≃ PartialMatchingSurgery.Remaining p q :=
  (flatten α p hfp).trans (rename α p q hpq hfp)
lemma coordinates_val (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    (coordinates α p q hpq hfp x).val=Equiv.swap q (r α p) (BandEuler.val p (r α p) (pr α p hfp) x) := rfl

lemma partner_commutes (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    coordinates α p q hpq hfp (BandEuler.partner α hi p (r α p) (pr α p hfp) rfl x)=
      PartialMatchingSurgery.partner α hi p q hpq hfp hfq (coordinates α p q hpq hfp x) := by
  apply Subtype.ext
  rw [coordinates_val,BandEuler.partner_val]
  change Equiv.swap q (α p) (α (BandEuler.val p (α p) (pr α p hfp) x))=
    PartialMatchingSurgery.splice α p q (Equiv.swap q (α p) (BandEuler.val p (α p) (pr α p hfp) x))
  let v := BandEuler.val p (α p) (pr α p hfp) x
  change Equiv.swap q (α p) (α v)=PartialMatchingSurgery.splice α p q (Equiv.swap q (α p) v)
  have hvp : v≠p := BandEuler.val_ne_p _ _ _ x
  have hvr : v≠α p := BandEuler.val_ne_q _ _ _ x
  have havp : α v≠p := fun h=>hvr ((hi _).symm.trans (congrArg α h))
  have havr : α v≠α p := α.injective.ne hvp
  by_cases hvq : v=q
  · rw [hvq,Equiv.swap_apply_left,PartialMatchingSurgery.splice,hi p,ite_eq_left rfl]
    have hαq : α q≠q := hfq
    have hαqr : α q≠α p := α.injective.ne hpq.symm
    exact Equiv.swap_apply_of_ne_of_ne hαq hαqr
  · rw [Equiv.swap_apply_of_ne_of_ne hvq hvr,PartialMatchingSurgery.splice,ite_eq_right havp]
    by_cases havq : α v=q
    · rw [ite_eq_left havq,havq,Equiv.swap_apply_left]
    · rw [ite_eq_right havq,Equiv.swap_apply_of_ne_of_ne havq havr]

lemma bypass_value (f : Equiv.Perm O) (a : O) (x : Rest a) :
    (bypass f a x).val=if f x=a then f a else f x := by
  change Equiv.swap a (f a) (f x)=_
  by_cases h : f x=a
  · rw [ite_eq_left h,h,Equiv.swap_apply_left]
  · rw [ite_eq_right h,Equiv.swap_apply_of_ne_of_ne h (f.injective.ne x.property)]
lemma rotation_value (a b : O) (hab : a≠b) (x : BandEuler.Residual a b hab) :
    BandEuler.val a b hab (BandEuler.rotation σ a b hab x)=
      let f := BandEuler.switched σ a b
      let g := fun y=>if f y=a then f a else f y
      if g (BandEuler.val a b hab x)=b then g b else g (BandEuler.val a b hab x) := by
  let f := BandEuler.switched σ a b
  let g := fun y=>if f y=a then f a else f y
  change ((bypass (bypass f a) (BandEuler.q' a b hab) x).val).val=
    if g x.val.val=b then g b else g x.val.val
  have he : bypass f a x.val=BandEuler.q' a b hab ↔ g x.val.val=b := by
    rw [Subtype.ext_iff,bypass_value]
  by_cases hc : g x.val.val=b
  · rw [ite_eq_left hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_left (he.mpr hc)] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a (BandEuler.q' a b hab))
  · rw [ite_eq_right hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_right (fun h=>hc (he.mp h))] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a x.val)

include hsp hsq hpq in
lemma smoothing_value (r v : O) (hpr : p≠r) (hvp : v≠p) (hvr : v≠r) :
    let f := Equiv.swap p r*σ
    let g := fun y=>if f y=p then f p else f y
    Equiv.swap q r (if g v=r then g r else g v)=σ (Equiv.swap q r v) := by
  let f := Equiv.swap p r*σ
  let g := fun y=>if f y=p then f p else f y
  change Equiv.swap q r (if g v=r then g r else g v)=_
  by_cases hqr : q=r
  · subst r
    have hsvp : σ v≠p := fun h=>hvr (σ.injective (h.trans hsq.symm))
    have hsvq : σ v≠q := fun h=>hvp (σ.injective (h.trans hsp.symm))
    have hfv : f v=σ v := Equiv.swap_apply_of_ne_of_ne hsvp hsvq
    have hg : g v=σ v := by
      change (if f v=p then f p else f v)=σ v
      simp only [hfv,ite_eq_right hsvp]
    rw [hg,ite_eq_right hsvq,Equiv.swap_self]
    rfl
  · have hfp : f p=q := by
      dsimp only [f,Equiv.Perm.mul_apply]
      rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm hqr]
    have hG (y : O) (hyp : y≠p) (hyq : y≠q) : Equiv.swap q r (g y)=σ y := by
      have hsyp : σ y≠p := fun h=>hyq (σ.injective (h.trans hsq.symm))
      have hsyq : σ y≠q := fun h=>hyp (σ.injective (h.trans hsp.symm))
      by_cases hsyr : σ y=r
      · have hfy : f y=p := by simp only [f,Equiv.Perm.mul_apply,hsyr,Equiv.swap_apply_right]
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        rw [ite_eq_left hfy,hfp,Equiv.swap_apply_left,hsyr]
      · have hfy : f y=σ y := by
          exact Equiv.swap_apply_of_ne_of_ne hsyp hsyr
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        simp only [hfy,ite_eq_right hsyp,Equiv.swap_apply_of_ne_of_ne hsyq hsyr]
    by_cases hvq : v=q
    · have hfq : f q=r := by simp only [f,Equiv.Perm.mul_apply,hsq,Equiv.swap_apply_left]
      have hgq : g q=r := by
        change (if f q=p then f p else f q)=r
        simp only [hfq,ite_eq_right hpr.symm]
      rw [hvq,hgq,ite_eq_left rfl,Equiv.swap_apply_left]
      exact hG r hpr.symm (Ne.symm hqr)
    · have hgv : g v≠r := by
        intro he
        have hh := hG v hvp hvq
        rw [he,Equiv.swap_apply_right] at hh
        exact hvp (σ.injective (hh.symm.trans hsp.symm))
      rw [ite_eq_right hgv,Equiv.swap_apply_of_ne_of_ne hvq hvr]
      exact hG v hvp hvq

lemma rotation_commutes (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    coordinates α p q hpq hfp (BandEuler.rotation σ p (r α p) (pr α p hfp) x)=
      rotation σ p q hsp hsq (coordinates α p q hpq hfp x) := by
  apply Subtype.ext
  rw [coordinates_val,rotation_value]
  exact smoothing_value σ p q hpq hsp hsq (r α p)
    (BandEuler.val p (r α p) (pr α p hfp) x) (pr α p hfp)
    (BandEuler.val_ne_p _ _ _ x) (BandEuler.val_ne_q _ _ _ x)

variable [Fintype O]
/-- Suppressing an actual two-occurrence boundary splices its matching partners,
including the already-paired case, and preserves combinatorial genus zero. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hsp hsq)
      (PartialMatchingSurgery.partner α hi p q hpq hfp hfq) := by
  let e := coordinates α p q hpq hfp
  let σ₀ := BandEuler.rotation σ p (r α p) (pr α p hfp)
  let α₀ := BandEuler.partner α hi p (r α p) (pr α p hfp) rfl
  have hz₀ : MapEuler.GenusZero σ₀ α₀ := BandEuler.genusZero_all σ α hi p
    (r α p) (pr α p hfp) rfl hz
  have h := MapConjugation.genusZero e σ₀ α₀ hz₀
  have hσ : e.permCongr σ₀=rotation σ p q hsp hsq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact rotation_commutes σ α p q hpq hfp hsp hsq x
  have hα : e.permCongr α₀=PartialMatchingSurgery.partner α hi p q hpq hfp hfq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact partner_commutes α hi p q hpq hfp hfq x
  rwa [hσ,hα] at h

end TorsionFreeZeroDivisors.PartialSmoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
variable {O : Type} [Fintype O] (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
  (α : Equiv.Perm O) (hi : Function.Involutive α) (hfp : α p≠p) (hfq : α q≠q)
/-- The tightening operation also allows unrelated unpaired markers. Only the
actual two deleted letter occurrences are required to be nonfixed. -/
theorem partial_genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hpq hsp)
      (PartialMatchingSurgery.partner α hi p q hpq hfp hfq) :=
  PartialSmoothing.genusZero (isolate σ p q) α hi p q hpq hfp hfq
    (isolate_p σ p q hpq hsp) (isolate_q σ p q) (isolate_genusZero σ p q hsp α hi hz)
end TorsionFreeZeroDivisors.Tightening
end
end OAI
