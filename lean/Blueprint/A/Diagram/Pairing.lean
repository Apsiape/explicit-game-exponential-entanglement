import Blueprint.A.Diagram.Map

/-! Proof port from OpenAI/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-APACHE-2.0-OpenAI and PROVENANCE.json.
Modified: selected generic namespaces, narrowed imports, split modules for Lean 4.35.0. -/

namespace OAI
noncomputable section
set_option maxHeartbeats 800000

namespace TorsionFreeZeroDivisors.WordPairing

section
variable {A : Type*} {n : ℕ}

structure Data (inv : A → A) (label : Fin n → A) where
  partner : Equiv.Perm (Fin n)
  involutive : Function.Involutive partner
  distinct : ∀ i,partner i≠i
  compatible : ∀ i,label (partner i)=inv (label i)
  noncrossing : ∀ i j,i<j → j<partner i → partner i<partner j → False

namespace Ear
variable (k : ℕ)
def raise (i : Fin n) : Fin (n+2) := ⟨if i.val<k then i.val else i.val+2,by
  split_ifs with h <;> omega⟩
lemma raise_lt (i j : Fin n) : raise k i<raise k j ↔ i<j := by
  simp only [raise,Fin.lt_def]
  split_ifs <;> omega
lemma raise_injective : Function.Injective (raise (n:=n) k) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  simp only [raise] at hh
  split_ifs at hh <;> omega
lemma raise_avoid (i : Fin n) : (raise k i).val≠k ∧ (raise k i).val≠k+1 := by
  simp only [raise]
  split_ifs <;> omega

def insert (hk : k≤n) : Fin n⊕Bool → Fin (n+2)
  | .inl i => raise k i
  | .inr false => ⟨k,by omega⟩
  | .inr true => ⟨k+1,by omega⟩
lemma insert_injective (hk : k≤n) : Function.Injective (insert k hk) := by
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (raise_injective k he)
    | inr b =>
      have hh := congrArg Fin.val he
      have ha := raise_avoid k i
      cases b <;> simp only [insert] at hh <;> omega
  | inr b =>
    cases y with
    | inl i =>
      have hh := congrArg Fin.val he
      have ha := raise_avoid k i
      cases b <;> simp only [insert] at hh <;> omega
    | inr c =>
      have hh := congrArg Fin.val he
      cases b <;> cases c <;> simp only [insert] at hh <;> first | rfl | omega
lemma insert_surjective (hk : k≤n) : Function.Surjective (insert k hk) := by
  intro y
  by_cases h : y.val<k
  · refine ⟨.inl ⟨y.val,by omega⟩,?_⟩
    apply Fin.ext
    simp only [insert,raise,ite_eq_left h]
  · by_cases he : y.val=k
    · exact ⟨.inr false,Fin.ext he.symm⟩
    · by_cases he' : y.val=k+1
      · exact ⟨.inr true,Fin.ext he'.symm⟩
      · refine ⟨.inl ⟨y.val-2,by omega⟩,?_⟩
        apply Fin.ext
        have hh : ¬y.val-2<k := by omega
        simp only [insert,raise,ite_eq_right hh]
        omega

def equiv (hk : k≤n) : Fin n⊕Bool ≃ Fin (n+2) :=
  Equiv.ofBijective (insert k hk) ⟨insert_injective k hk,insert_surjective k hk⟩
@[simp] lemma equiv_left (hk : k≤n) (i : Fin n) : equiv k hk (.inl i)=raise k i := rfl
@[simp] lemma equiv_false (hk : k≤n) : (equiv k hk (.inr false)).val=k := rfl
@[simp] lemma equiv_true (hk : k≤n) : (equiv k hk (.inr true)).val=k+1 := rfl

variable {inv : A → A} {label : Fin n → A} (d : Data inv label)
def sumPartner : Equiv.Perm (Fin n⊕Bool) := Equiv.sumCongr d.partner Equiv.boolNot

def partner (hk : k≤n) : Equiv.Perm (Fin (n+2)) :=
  (equiv k hk).permCongr (sumPartner d)
lemma partner_apply (hk : k≤n) (i : Fin n⊕Bool) :
    partner k d hk (equiv k hk i)=equiv k hk (sumPartner d i) := by
  simp only [partner,Equiv.permCongr_apply,Equiv.symm_apply_apply]

lemma involutive (hk : k≤n) : Function.Involutive (partner k d hk) := by
  intro i
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  rw [partner_apply,partner_apply]
  congr 1
  cases i with
  | inl i => exact congrArg Sum.inl (d.involutive i)
  | inr b => cases b <;> rfl
lemma distinct (hk : k≤n) (i : Fin (n+2)) : partner k d hk i≠i := by
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  rw [partner_apply]
  intro he
  have hh := (equiv k hk).injective he
  cases i with
  | inl i => exact d.distinct i (Sum.inl.inj hh)
  | inr b => cases b <;> cases hh

lemma noncrossing (hk : k≤n) : ∀ i j : Fin (n+2),
    i<j → j<partner k d hk i → partner k d hk i<partner k d hk j → False := by
  intro i j hij hjp hpp
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  obtain ⟨j,rfl⟩ := (equiv k hk).surjective j
  rw [partner_apply] at hjp hpp
  rw [partner_apply] at hpp
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact d.noncrossing i j ((raise_lt k _ _).mp hij)
        ((raise_lt k _ _).mp hjp) ((raise_lt k _ _).mp hpp)
    | inr b =>
      cases b with
      | false =>
        change k < (raise k (d.partner i)).val at hjp
        change (raise k (d.partner i)).val < k+1 at hpp
        omega
      | true =>
        change k+1 < (raise k (d.partner i)).val at hjp
        change (raise k (d.partner i)).val < k at hpp
        omega
  | inr b =>
    cases b with
    | false =>
      change k < (equiv k hk j).val at hij
      change (equiv k hk j).val < k+1 at hjp
      omega
    | true =>
      change k+1 < (equiv k hk j).val at hij
      change (equiv k hk j).val < k at hjp
      omega
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
variable (d : Data inv label)
lemma reindex_apply (e : Fin n ≃o Fin m) (i : Fin n) :
    e.toEquiv.permCongr d.partner (e i)=e (d.partner i) := by
  change e (d.partner (e.symm (e i)))=e (d.partner i)
  rw [e.symm_apply_apply]
def reindex (e : Fin n ≃o Fin m) (label' : Fin m → A)
    (hl : ∀ i,label' (e i)=label i) : Data inv label' where
  partner := e.toEquiv.permCongr d.partner
  involutive := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply,d.reindex_apply,d.involutive]
  distinct := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply]
    exact fun he=>d.distinct i (e.injective he)
  compatible := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply,hl,hl]
    exact d.compatible i
  noncrossing := by
    intro i j hij hjp hpp
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    rw [d.reindex_apply] at hjp
    rw [d.reindex_apply,d.reindex_apply] at hpp
    exact d.noncrossing i j ((e.lt_iff_lt).mp hij)
      ((e.lt_iff_lt).mp hjp) ((e.lt_iff_lt).mp hpp)
end Data

namespace Ear
variable (k : ℕ) (hk : k≤n) (a : A)
def labels (i : Fin (n+2)) : A :=
  Sum.elim label (fun b=>if b then inv a else a) ((equiv k hk).symm i)
@[simp] lemma labels_left (i : Fin n) :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inl i))=label i := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inl]
@[simp] lemma labels_false :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inr false))=a := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inr,Bool.false_eq_true,ite_false]
@[simp] lemma labels_true :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inr true))=inv a := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inr,ite_true]

def data (d : Data inv label) (ha : inv (inv a)=a) :
    Data inv (labels (label:=label) (inv:=inv) k hk a) where
  partner := partner k d hk
  involutive := involutive k d hk
  distinct := distinct k d hk
  compatible := by
    intro i
    obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
    rw [partner_apply]
    cases i with
    | inl i =>
      change labels k hk a (equiv k hk (.inl (d.partner i)))=_
      rw [labels_left,labels_left]
      exact d.compatible i
    | inr b =>
      cases b with
      | false => exact (labels_true k hk a).trans (congrArg inv (labels_false k hk a).symm)
      | true =>
        change labels k hk a (equiv k hk (.inr false))=inv (labels k hk a (equiv k hk (.inr true)))
        rw [labels_false,labels_true,ha]
  noncrossing := noncrossing k d hk
end Ear

namespace ListInsert
variable (u v : List A) (a b : A)
lemma get_old (i : ℕ) (hi : i<(u++v).length) :
    (u++a::b::v)[if i<u.length then i else i+2]'(by split_ifs <;> simp only [List.length_append,List.length_cons] at * <;> omega)=
      (u++v)[i] := by
  by_cases h : i<u.length
  · simp only [ite_eq_left h,List.getElem_append_left h]
  · have hh : ¬i+2<u.length := by omega
    have he : i+2-u.length=(i-u.length)+2 := by omega
    simp only [ite_eq_right h,List.getElem_append,dite_eq_right h,dite_eq_right hh,he,List.getElem_cons_succ]
lemma get_first :
    (u++a::b::v)[u.length]'(by simp only [List.length_append,List.length_cons];omega)=a := by
  simp only [List.getElem_append,dite_eq_right (Nat.lt_irrefl _),Nat.sub_self,List.getElem_cons_zero]
lemma get_second :
    (u++a::b::v)[u.length+1]'(by simp only [List.length_append,List.length_cons];omega)=b := by
  have hh : ¬u.length+1<u.length := by omega
  simp only [List.getElem_append,dite_eq_right hh,Nat.add_sub_cancel_left,List.getElem_cons_succ,List.getElem_cons_zero]
end ListInsert

end
variable {A : Type*}
namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
lemma length_eq : (u++v).length+2=(u++a::inv a::v).length := by
  simp only [List.length_append,List.length_cons]
  omega

def orderIso : Fin ((u++v).length+2) ≃o Fin (u++a::inv a::v).length :=
  Fin.castOrderIso (length_eq u v inv a)

lemma labels_eq (i : Fin ((u++v).length+2)) :
    (u++a::inv a::v).get (orderIso u v inv a i)=
      Ear.labels (label:=(u++v).get) (inv:=inv) u.length
        (by simp only [List.length_append];omega) a i := by
  obtain ⟨i,rfl⟩ := (Ear.equiv u.length (show u.length≤(u++v).length by
    simp only [List.length_append];omega)).surjective i
  cases i with
  | inl i =>
    rw [Ear.labels_left]
    change (u++a::inv a::v)[if i.val<u.length then i.val else i.val+2]'(by
      have hi := i.isLt
      split_ifs <;> simp only [List.length_append,List.length_cons] at * <;> omega)=
      (u++v)[i.val]
    exact get_old u v a (inv a) i.val i.isLt
  | inr b =>
    cases b with
    | false =>
      rw [Ear.labels_false]
      exact get_first u v a (inv a)
    | true =>
      rw [Ear.labels_true]
      exact get_second u v a (inv a)

def data (d : Data inv (u++v).get) (ha : inv (inv a)=a) :
    Data inv (u++a::inv a::v).get :=
  (Ear.data u.length (by simp only [List.length_append];omega) a d ha).reindex
    (orderIso u v inv a) _ (labels_eq u v inv a)
end ListInsert

def inverseLetter (p : A × Bool) : A × Bool := (p.1,!p.2)
lemma inverseLetter_involutive : Function.Involutive (inverseLetter (A:=A)) := by
  intro p
  cases p with
  | mk a b => cases b <;> rfl

def emptyData : Data (inverseLetter (A:=A)) ([] : List (A×Bool)).get where
  partner := Equiv.refl _
  involutive := fun _=>rfl
  distinct i := Fin.elim0 i
  compatible i := Fin.elim0 i
  noncrossing i := Fin.elim0 i

theorem of_reduction {w : List (A×Bool)} (h : FreeGroup.Red w []) :
    Nonempty (Data inverseLetter w.get) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨emptyData⟩
  | @head x y hxy hy ih =>
    cases hxy with
    | @not u v a b =>
      obtain ⟨d⟩ := ih
      exact ⟨ListInsert.data u v inverseLetter (a,b) d (inverseLetter_involutive _)⟩

theorem of_identity {w : List (A×Bool)} (h : FreeGroup.mk w=1) :
    Nonempty (Data inverseLetter w.get) := by
  classical
  have he : FreeGroup.reduce w=[] := by
    have hh := FreeGroup.reduce.sound h
    exact hh
  apply of_reduction
  rw [←he]
  exact FreeGroup.reduce.red

end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.Ear
open PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
lemma rotate_val (i : Fin n) : (finRotate n i).val=if i.val+1<n then i.val+1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    simp only [Fin.ext_iff,Fin.val_last]
    split_ifs <;> have := i.isLt <;> omega

def previous (k : ℕ) (hk : k≤n) (hn : 0<n) : Fin n :=
  ⟨if k=0 then n-1 else k-1,by split_ifs <;> omega⟩
variable (k : ℕ) (hk : k≤n) (hn : 0<n)
lemma previous_rotate : finRotate (n+2) (raise k (previous k hk hn))=equiv k hk (.inr false) := by
  apply Fin.ext
  change (finRotate (n+2) (raise k (previous k hk hn))).val=k
  rw [rotate_val]
  simp only [raise,previous]
  split_ifs <;> omega
lemma rotate_old (i : Fin n) (hi : i≠previous k hk hn) :
    finRotate (n+2) (raise k i)=raise k (finRotate n i) := by
  apply Fin.ext
  have hi' : i.val≠(previous k hk hn).val := fun h=>hi (Fin.ext h)
  rw [rotate_val]
  simp only [raise,rotate_val,previous] at *
  have hb := i.isLt
  split_ifs at * <;> omega
lemma rotate_false : finRotate (n+2) (equiv k hk (.inr false))=equiv k hk (.inr true) := by
  apply Fin.ext
  rw [rotate_val]
  change (if k+1<n+2 then k+1 else 0)=k+1
  rw [ite_eq_left (by omega)]
lemma rotate_true : finRotate (n+2) (equiv k hk (.inr true))=
    raise k (finRotate n (previous k hk hn)) := by
  apply Fin.ext
  rw [rotate_val]
  change (if k+1+1<n+2 then k+1+1 else 0)=_
  simp only [raise,rotate_val,previous]
  split_ifs <;> omega

lemma rotation_transport (i : Fin n⊕Bool) :
    finRotate (n+2) (equiv k hk i)=equiv k hk
      (InsertedRotation.rotation (finRotate n) (previous k hk hn) i) := by
  cases i with
  | inl i =>
    by_cases hi : i=previous k hk hn
    · subst i
      rw [InsertedRotation.rotation_p,equiv_left]
      exact previous_rotate k hk hn
    · rw [InsertedRotation.rotation_left _ _ i hi,equiv_left,equiv_left]
      exact rotate_old k hk hn i hi
  | inr b =>
    cases b with
    | false => rw [InsertedRotation.rotation_false]; exact rotate_false k hk
    | true => rw [InsertedRotation.rotation_true,equiv_left]; exact rotate_true k hk hn

lemma rotation_eq : (equiv k hk).permCongr
    (InsertedRotation.rotation (finRotate n) (previous k hk hn))=finRotate (n+2) := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  exact (rotation_transport k hk hn i).symm

variable (d : Data inv label)
lemma face_eq : (equiv k hk).permCongr
    (InsertedRotation.face (finRotate n) d.partner (previous k hk hn))=
    partner k d hk *finRotate (n+2) := by
  rw [InsertedRotation.face,PermutationTransport.mul,rotation_eq k hk hn]
  rfl

include hn in
theorem face_count :
    Fintype.card (Cycle (d.partner*finRotate n))+1≤
      Fintype.card (Cycle (partner k d hk*finRotate (n+2))) := by
  rw [←face_eq k hk hn d,PermutationTransport.card_cycles]
  exact InsertedRotation.face_count _ _ _

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
lemma card_identity : Fintype.card (Cycle (1 : Equiv.Perm O))=Fintype.card O := by
  apply (Fintype.card_of_bijective (f:=cycle (1 : Equiv.Perm O)) ?_).symm
  refine ⟨?_,cycle_surjective _⟩
  intro x y h
  exact ((cycle_eq _).mp h).eq_of_left rfl
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

/-- The disk Euler estimate for the actual circle rotation and word matching.
The empty word is distinguished, since it has no boundary occurrences. -/
def DiskEuler (d : Data inv label) : Prop :=
  n=0 ∨ n+2≤2*Fintype.card (Cycle (d.partner*finRotate n))

lemma Data.reindex_euler (d : Data inv label) (h : n=m) (label' : Fin m→A)
    (hl : ∀i,label' (Fin.castOrderIso h i)=label i) (hd : DiskEuler d) :
    DiskEuler (d.reindex (Fin.castOrderIso h) label' hl) := by
  subst m
  exact hd

namespace Ear
variable (k : ℕ) (hk : k≤n) (d : Data inv label)
lemma empty_rotation (hn : n=0) : partner k d hk=finRotate (n+2) := by
  subst n
  have he : k=0 := by omega
  subst k
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (equiv 0 hk).surjective i
  rw [partner_apply]
  cases i with
  | inl i => exact i.elim0
  | inr b => cases b <;> rfl

lemma euler (hd : DiskEuler d) :
    n+2+2≤2*Fintype.card (Cycle (partner k d hk*finRotate (n+2))) := by
  by_cases he : n=0
  · have hrot := empty_rotation k hk d he
    have hf : partner k d hk*finRotate (n+2)=1 := by
      apply Equiv.ext
      intro i
      rw [Equiv.Perm.mul_apply,←hrot]
      exact involutive k d hk i
    rw [hf,card_identity,Fintype.card_fin,he]
  · have hn : 0<n := Nat.pos_of_ne_zero he
    have hc := face_count k hk hn d
    rcases hd with hh|hh
    · exact (he hh).elim
    · omega
end Ear

namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
lemma data_euler (d : Data inv (u++v).get) (ha : inv (inv a)=a) (hd : DiskEuler d) :
    DiskEuler (data u v inv a d ha) := by
  apply Data.reindex_euler
  apply Or.inr
  exact Ear.euler u.length (by simp only [List.length_append];omega) d hd
end ListInsert

/-- The face-count input is now proved for the matching constructed from literal
free cancellation. This does not yet claim a multi-disk PL realization. -/
theorem of_reduction_euler {w : List (A×Bool)} (h : FreeGroup.Red w []) :
    ∃ d : Data inverseLetter w.get,DiskEuler d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨emptyData,Or.inl rfl⟩
  | @head x y hxy hy ih =>
    cases hxy with
    | @not u v a b =>
      obtain ⟨d,hd⟩ := ih
      refine ⟨ListInsert.data u v inverseLetter (a,b) d (inverseLetter_involutive _),?_⟩
      exact ListInsert.data_euler u v inverseLetter (a,b) d (inverseLetter_involutive _) hd

theorem of_identity_euler {w : List (A×Bool)} (h : FreeGroup.mk w=1) :
    ∃ d : Data inverseLetter w.get,DiskEuler d := by
  classical
  have he : FreeGroup.reduce w=[] := FreeGroup.reduce.sound h
  apply of_reduction_euler
  rw [←he]
  exact FreeGroup.reduce.red

end
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
/-- Every nonempty finite noncrossing perfect matching has a literal adjacent
ear, obtained by minimizing the positive distance between matched positions. -/
theorem adjacent_ear (d : Data inv label) (hn : 0 < n) :
    ∃i : Fin n,(d.partner i).val=i.val+1 := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i=> i < d.partner i)
  have hs : s.Nonempty := by
    let z : Fin n := ⟨0,hn⟩
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    have he := d.distinct z
    have hv : (d.partner z).val ≠ 0 := by intro h;exact he (Fin.ext h)
    change 0 < (d.partner z).val
    omega
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image s (fun i=> (d.partner i).val-i.val) hs
  have hip : i < d.partner i := (Finset.mem_filter.mp hi).2
  refine ⟨i,?_⟩
  by_contra he
  have hgap : i.val+1 < (d.partner i).val := by change i.val < (d.partner i).val at hip;omega
  let j : Fin n := ⟨i.val+1,lt_trans hgap (d.partner i).isLt⟩
  have hij : i < j := by change i.val < i.val+1;omega
  have hjp : j < d.partner i := hgap
  have hpj : j < d.partner j := by
    by_contra h
    have hpj : d.partner j < j := lt_of_le_of_ne (le_of_not_gt h) (d.distinct j)
    have hai : d.partner j ≠ i := by
      intro h
      have h' : j=d.partner i := (d.involutive j).symm.trans (congrArg d.partner h)
      exact (ne_of_lt hjp) h'
    have hapi : d.partner j < i := by
      have haival : (d.partner j).val ≠ i.val := by intro hh;exact hai (Fin.ext hh)
      change (d.partner j).val < i.val
      change (d.partner j).val < i.val+1 at hpj
      omega
    apply d.noncrossing (d.partner j) i hapi
    · simpa only [d.involutive j] using hij
    · simpa only [d.involutive j] using hjp
  have upper : d.partner j < d.partner i := by
    have hnlt : ¬d.partner i < d.partner j := fun h=> d.noncrossing i j hij hjp h
    have hne : d.partner j ≠ d.partner i := fun hh=> ne_of_gt hij (d.partner.injective hh)
    exact lt_of_le_of_ne (le_of_not_gt hnlt) hne
  have hmem : j∈s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpj⟩
  have hm := hmin j hmem
  change (d.partner i).val-i.val ≤ (d.partner j).val-(i.val+1) at hm
  change (d.partner j).val < (d.partner i).val at upper
  omega
end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.EraseEar
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A}
  (d : Data inv label) (k : ℕ) (hk : k≤n)
  (hpair : d.partner (Ear.equiv k hk (.inr false))=Ear.equiv k hk (.inr true))
include hpair in
lemma back : d.partner (Ear.equiv k hk (.inr true))=Ear.equiv k hk (.inr false) :=
  (congrArg d.partner hpair).symm.trans (d.involutive _)
include hpair in
lemma remains (i : Fin n) : ∃j : Fin n,Ear.raise k j=d.partner (Ear.raise k i) := by
  obtain ⟨a,ha⟩ := (Ear.equiv k hk).surjective (d.partner (Ear.raise k i))
  cases a with
  | inl j => exact ⟨j,ha⟩
  | inr b =>
    cases b with
    | false =>
      have he := hpair.symm.trans ((congrArg d.partner ha).trans (d.involutive _))
      change Ear.equiv k hk (.inr true)=Ear.equiv k hk (.inl i) at he
      cases (Ear.equiv k hk).injective he
    | true =>
      have he := (back d k hk hpair).symm.trans ((congrArg d.partner ha).trans (d.involutive _))
      change Ear.equiv k hk (.inr false)=Ear.equiv k hk (.inl i) at he
      cases (Ear.equiv k hk).injective he

def lower (i : Fin n) : Fin n := Classical.choose (remains d k hk hpair i)
lemma lower_spec (i : Fin n) : Ear.raise k (lower d k hk hpair i)=d.partner (Ear.raise k i) :=
  Classical.choose_spec (remains d k hk hpair i)
lemma lower_involutive : Function.Involutive (lower d k hk hpair) := by
  intro i
  apply Ear.raise_injective k
  rw [lower_spec,lower_spec,d.involutive]

def data : Data inv (fun i=>label (Ear.raise (n:=n) k i)) where
  partner := ⟨lower d k hk hpair,lower d k hk hpair,
    lower_involutive d k hk hpair,lower_involutive d k hk hpair⟩
  involutive := lower_involutive d k hk hpair
  distinct i := by
    intro he
    have hh := congrArg (Ear.raise k) he
    change Ear.raise k (lower d k hk hpair i)=Ear.raise k i at hh
    rw [lower_spec] at hh
    exact d.distinct _ hh
  compatible i := by
    change label (Ear.raise k (lower d k hk hpair i))=inv (label (Ear.raise k i))
    rw [lower_spec,d.compatible]
  noncrossing i j hij hji hpp := by
    apply d.noncrossing (Ear.raise k i) (Ear.raise k j) ((Ear.raise_lt k i j).mpr hij)
    · rw [←lower_spec d k hk hpair i]
      exact (Ear.raise_lt k _ _).mpr hji
    · rw [←lower_spec d k hk hpair i,←lower_spec d k hk hpair j]
      exact (Ear.raise_lt k _ _).mpr hpp

lemma recover : Ear.partner k (data d k hk hpair) hk=d.partner := by
  apply Equiv.ext
  intro i
  obtain ⟨a,rfl⟩ := (Ear.equiv k hk).surjective i
  rw [Ear.partner_apply]
  cases a with
  | inl i => exact lower_spec d k hk hpair i
  | inr b =>
    cases b with
    | false => exact hpair.symm
    | true => exact (back d k hk hpair).symm

lemma euler (hd : DiskEuler (data d k hk hpair)) : DiskEuler d := by
  apply Or.inr
  rw [←recover d k hk hpair]
  exact Ear.euler k hk (data d k hk hpair) hd
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
/-- Every literal finite noncrossing inverse-letter matching has the disk Euler
estimate, independently of its choice as a free cancellation witness. -/
theorem Data.diskEuler {n : ℕ} {label : Fin n → A} (d : Data inv label) : DiskEuler d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact Or.inl rfl
    | succ n =>
      cases n with
      | zero => exact False.elim (d.distinct 0 (Fin.ext (by have h := (d.partner 0).isLt; omega)))
      | succ n =>
        obtain ⟨i,hi⟩ := adjacent_ear d (by omega)
        have hk : i.val ≤ n := by have hb := (d.partner i).isLt;omega
        have hp : d.partner (Ear.equiv i.val hk (.inr false))=
            Ear.equiv i.val hk (.inr true) := by
          have he : Ear.equiv i.val hk (.inr false)=i := Fin.ext rfl
          rw [he]
          exact Fin.ext hi
        apply EraseEar.euler d i.val hk hp
        exact ih n (by omega) (EraseEar.data d i.val hk hp)
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.MapEuler
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
lemma component_sameCycle {x y : O} (h : σ.SameCycle x y) :
    component σ α x=component σ α y := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have hh := PermutationCycles.invariant_pow σ (component σ α) (component_rotation σ α) k x
  rw [hk] at hh
  exact hh.symm
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
open MapEuler PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin n→A} (d : Data inv label)
lemma rotate_sameCycle (hn : 2≤n) (x y : Fin n) : (finRotate n).SameCycle x y := by
  apply (isCycle_finRotate_of_le hn).sameCycle
  · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn];exact Finset.mem_univ _)
  · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn];exact Finset.mem_univ _)
/-- The noncrossing cancellation matching has actual combinatorial genus zero,
not just a scalar disk face estimate. Nonempty words (necessarily of length at
least two) have a single map component; the empty case is separate. -/
theorem Data.genusZero : GenusZero (finRotate n) d.partner := by
  by_cases hn : n=0
  · subst n
    have hi : IsEmpty (Fin 0) := inferInstance
    have hV : IsEmpty (Cycle (finRotate 0)) := inferInstance
    have hF : IsEmpty (Cycle (d.partner*finRotate 0)) := inferInstance
    have hC : IsEmpty (Component (finRotate 0) d.partner) := inferInstance
    simp only [GenusZero,Nat.card_of_isEmpty,mul_zero,add_zero]
    simp only [Equiv.Perm.support,Finset.univ_eq_empty,Finset.filter_empty,Finset.card_empty]
  have hn2 : 2≤n := by
    by_contra hh
    have he : n=1 := by omega
    subst n
    exact d.distinct 0 (Subsingleton.elim _ _)
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let : Subsingleton (Cycle (finRotate n)) := ⟨by
    intro x y
    obtain ⟨a,rfl⟩ := cycle_surjective _ x
    obtain ⟨b,rfl⟩ := cycle_surjective _ y
    exact (cycle_eq _).mpr (rotate_sameCycle hn2 a b)⟩
  let : Subsingleton (Component (finRotate n) d.partner) := ⟨by
    intro x y
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Quotient.mk_surjective y
    exact component_sameCycle _ _ (rotate_sameCycle hn2 a b)⟩
  let : Nonempty (Cycle (finRotate n)) := ⟨cycle _ ⟨0,by omega⟩⟩
  let : Nonempty (Component (finRotate n) d.partner) := ⟨component _ _ ⟨0,by omega⟩⟩
  have hV : Nat.card (Cycle (finRotate n))=1 := Nat.card_unique
  have hC : Nat.card (Component (finRotate n) d.partner)=1 := Nat.card_unique
  have hd := (d.diskEuler).resolve_left hn
  simp only [←Nat.card_eq_fintype_card] at hd
  apply genusZero_of_lower (finRotate n) d.partner d.involutive
  rw [hV,hC]
  have he := d.distinct
  simp only [Equiv.Perm.support,he,ne_eq,not_false_eq_true,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
  omega
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.DeleteCycle
open scoped Classical
variable {O : Type} (σ : Equiv.Perm O) (p : O)
lemma bypass_fixed (h : σ p=p) : bypass σ p=restrict σ p h := by
  ext x
  change Equiv.swap p (σ p) (σ x)=σ x
  rw [h,Equiv.swap_self]
  rfl
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.IsolatedDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
def classify (x : O) : Option (Component (restrict σ p hs) (restrict α p ha)) :=
  if hx : x=p then none else some (component _ _ ⟨x,hx⟩)
lemma classify_rotation (x : O) : classify σ α p hs ha (σ x)=classify σ α p hs ha x := by
  by_cases hx : x=p
  · subst x;rw [hs]
  · rw [classify,dite_eq_right ((invariant σ p hs x).mpr hx),classify,dite_eq_right hx]
    exact congrArg some (component_rotation (restrict σ p hs) (restrict α p ha) ⟨x,hx⟩)
lemma classify_partner (x : O) : classify σ α p hs ha (α x)=classify σ α p hs ha x := by
  by_cases hx : x=p
  · subst x;rw [ha]
  · rw [classify,dite_eq_right ((invariant α p ha x).mpr hx),classify,dite_eq_right hx]
    exact congrArg some (component_partner (restrict σ p hs) (restrict α p ha) ⟨x,hx⟩)
def project : Component σ α → Option (Component (restrict σ p hs) (restrict α p ha)) :=
  MapEuler.lift σ α (classify σ α p hs ha) (classify_rotation σ α p hs ha) (classify_partner σ α p hs ha)
def inclusion : Component (restrict σ p hs) (restrict α p ha) → Component σ α :=
  MapEuler.lift _ _ (fun x : Rest p=>component σ α x)
    (fun x=>component_rotation σ α x) (fun x=>component_partner σ α x)
lemma project_injective : Function.Injective (project σ α p hs ha) := by
  intro c d he
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective d
  change classify σ α p hs ha x=classify σ α p hs ha y at he
  by_cases hx : x=p
  · subst x
    have hy : y=p := by
      by_contra hy
      simp [classify,hy] at he
    subst y;rfl
  · by_cases hy : y=p
    · subst y;simp [classify,hx] at he
    · simp only [classify,dite_eq_right hx,dite_eq_right hy,Option.some.injEq] at he
      exact congrArg (inclusion σ α p hs ha) he
lemma project_surjective : Function.Surjective (project σ α p hs ha) := by
  intro c
  cases c with
  | none=>exact ⟨component σ α p,by simp [project,MapEuler.lift,classify,component]⟩
  | some c=>
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    refine ⟨component σ α x,?_⟩
    change classify σ α p hs ha x=some (component _ _ x)
    simp only [classify,dite_eq_right x.property]
def componentEquiv : Component σ α ≃ Option (Component (restrict σ p hs) (restrict α p ha)) :=
  Equiv.ofBijective (project σ α p hs ha) ⟨project_injective σ α p hs ha,project_surjective σ α p hs ha⟩
variable [Fintype O]
lemma component_count : Nat.card (Component σ α)=Nat.card (Component (restrict σ p hs) (restrict α p ha))+1 := by
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using Nat.card_congr (componentEquiv σ α p hs ha)
include hs in
/-- Deleting an isolated unpaired occurrence removes one vertex, one face and
one actual connected component; genus zero is preserved also in the empty case. -/
theorem genusZero (hz : GenusZero σ α) :
    GenusZero (bypass σ p) (restrict α p ha) := by
  rw [bypass_fixed σ p hs]
  have hv := fixed_count σ p hs
  have hf := fixed_count (α*σ) p (show (α*σ) p=p by change α (σ p)=p;rw [hs,ha])
  have hc := component_count σ α p hs ha
  have he := MapDeletion.support_count α p ha
  simp only [←Nat.card_eq_fintype_card] at hv hf
  have hface : restrict (α*σ) p (show (α*σ) p=p by change α (σ p)=p;rw [hs,ha])=
      restrict α p ha*restrict σ p hs := by ext x;rfl
  rw [hface] at hf
  dsimp only [GenusZero] at hz ⊢
  have hsup : (restrict α p ha).support.card=α.support.card := by
    convert he using 1
  have hh : 2*Nat.card (PermutationCycles.Cycle (restrict σ p hs))+
      2*Nat.card (PermutationCycles.Cycle (restrict α p ha*restrict σ p hs))=
      (restrict α p ha).support.card+4*Nat.card (Component (restrict σ p hs) (restrict α p ha)) := by omega
  have hinst : ∀ (i j : Fintype (Rest p)) (d e : DecidableEq (Rest p)),
      @Equiv.Perm.support (Rest p) d i (restrict α p ha)=
      @Equiv.Perm.support (Rest p) e j (restrict α p ha) := by
    intro i j d e
    cases Subsingleton.elim i j
    cases Subsingleton.elim d e
    rfl
  convert hh using 1
  congr 1
  exact congrArg Finset.card (hinst _ _ _ _)
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
/-- Unconditional deletion of an unpaired occurrence, including isolated
vertices/components. -/
theorem genusZero_delete_all (hz : GenusZero σ α) : GenusZero (bypass σ p) (restrict α p ha) := by
  by_cases hs : σ p=p
  · exact IsolatedDeletion.genusZero σ α p hs ha hz
  · exact genusZero_delete σ α p ha hs hz
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
include hi hpair in
/-- Paired-band deletion preserves genus zero without any degree or face
nondegeneracy assumptions. Empty residual maps, isolated disks, monogons, digons,
and split components are all included. This is purely a permutation-map result,
not an assertion that an essential sphere survives the surgery. -/
theorem genusZero_all (hz : GenusZero σ α) :
    GenusZero (rotation σ p q hpq) (partner α hi p q hpq hpair) := by
  have h₀ := switched_genusZero σ α hi p q hpq hpair hz
  have h₁ := MapDeletion.genusZero_delete_all (switched σ p q) (adjusted α p q) p
    (adjusted_p α hi p q hpair) h₀
  have h₂ := MapDeletion.genusZero_delete_all (bypass (switched σ p q) p) (α₁ α hi p q hpair)
    (q' p q hpq) (α₁_q α hi p q hpq hpair) h₁
  exact (genusZero_fintype _ _ _ _).mp h₂
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
/-- Exact Euler lower bound used by the source interval estimate, extracted
from actual combinatorial genus zero. No connectivity is assumed: one actual
occurrence suffices to make the component count positive. -/
theorem euler_of_genusZero [Nonempty O] (hz : GenusZero σ α) (hf : ∀x,α x≠x) :
    Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (α*σ)) := by
  let : Nonempty (Component σ α) := ⟨component σ α (Classical.choice inferInstance)⟩
  have hc : 0<Nat.card (Component σ α) := Nat.card_pos
  have he : α.support.card=Fintype.card O := by
    simp only [Equiv.Perm.support,hf,ne_eq,not_false_eq_true,Finset.filter_true,Finset.card_univ]
  dsimp only [GenusZero] at hz
  simp only [Nat.card_eq_fintype_card] at hz hc
  rw [he] at hz
  omega
end TorsionFreeZeroDivisors.MapEuler
end
end OAI
