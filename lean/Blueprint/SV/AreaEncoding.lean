import Blueprint.SV.NumericEncoding

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic

abbrev ValidRelator (rfn : RelKey → Option Word) :=
  {p : RelKey × Word // rfn p.1=some p.2}

def relatorValue (rfn : RelKey → Option Word) (i : ValidRelator rfn) : FreeGroup Nat :=
  FreeGroup.mk i.val.2

def relationMap (rfn : RelKey → Option Word) :
    FreeGroup Nat →* PresentedGroup (Set.range (relatorValue rfn)) :=
  PresentedGroup.mk _

theorem relation_trivial (rfn : RelKey → Option Word) (k : RelKey) (r : Word)
    (hr : rfn k=some r) : relationMap rfn (FreeGroup.mk r)=1 :=
  PresentedGroup.one_of_mem (rels:=Set.range (relatorValue rfn)) ⟨⟨(k,r),hr⟩,rfl⟩

theorem group_word_eval {G : Type*} [Group G] (H : FreeGroup Nat →* G) (r : Word) :
    H (FreeGroup.mk r)=
      (r.map (fun a => if a.2 then H (FreeGroup.of a.1) else (H (FreeGroup.of a.1))⁻¹)).prod := by
  have hh : FreeGroup.lift (fun j => H (FreeGroup.of j))=H := by
    apply FreeGroup.ext_hom
    intro j
    simp
  rw [←hh,FreeGroup.lift_mk]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨j,b⟩ hb
  cases b <;> simp

theorem area_of_quotient (rfn : RelKey → Option Word) (w : Word)
    (hw : relationMap rfn (FreeGroup.mk w)=1) : ∃ n, HasAreaWith rfn w n := by
  obtain ⟨n,fs,hfs,heq⟩ := FiniteArea.exists_area_of_quotient (relatorValue rfn) (FreeGroup.mk w) hw
  let convertFactor : FiniteArea.Factor Nat (ValidRelator rfn) → Companion.Factor :=
    fun f => ⟨f.2.1.val.1,f.2.2,f.1.toWord⟩
  have hv (f : FiniteArea.Factor Nat (ValidRelator rfn)) :
      (rfn (convertFactor f).key).isSome=true := by
    change (rfn f.2.1.val.1).isSome=true
    rw [f.2.1.property]
    rfl
  have he (f : FiniteArea.Factor Nat (ValidRelator rfn)) :
      FreeGroup.mk (factorWordWith rfn (convertFactor f))=FiniteArea.factorValue (relatorValue rfn) f := by
    rcases f with ⟨g,⟨⟨k,r⟩,hr⟩,b⟩
    cases b <;>
      simp [convertFactor,factorWordWith,hr,FiniteArea.factorValue,relatorValue,
        ←FreeGroup.mul_mk,←FreeGroup.inv_mk,FreeGroup.mk_toWord,mul_assoc]
  refine ⟨n,fs.map convertFactor,by simpa using hfs,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact hv g
  · rw [mk_expandWith,List.map_map]
    simpa only [Function.comp_def,he] using heq

theorem area_map_consequence {α ι : Type} (R : ι → FreeGroup α) (w : FreeGroup α) (n : Nat)
    (ha : FiniteArea.Area R w n) (rfn : RelKey → Option Word)
    (phi : FreeGroup α →* FreeGroup Nat)
    (hr : ∀ i, relationMap rfn (phi (R i))=1) : relationMap rfn (phi w)=1 := by
  obtain ⟨fs,hfs,heq⟩ := ha
  let H := (relationMap rfn).comp phi
  have hf (f : FiniteArea.Factor α ι) : H (FiniteArea.factorValue R f)=1 := by
    rcases f with ⟨g,i,b⟩
    cases b <;> simp [H,FiniteArea.factorValue,hr]
  change H w=1
  rw [←heq,map_list_prod,List.map_map]
  simp only [Function.comp_def,hf]
  exact List.prod_map_one

theorem map_area {α ι : Type} (R : ι → FreeGroup α) (w : FreeGroup α) (n : Nat)
    (ha : FiniteArea.Area R w n) (rfn : RelKey → Option Word)
    (phi : FreeGroup α →* FreeGroup Nat)
    (hr : ∀ i, relationMap rfn (phi (R i))=1) :
    ∃ k, HasAreaWith rfn (phi w).toWord k := by
  apply area_of_quotient
  rw [FreeGroup.mk_toWord]
  exact area_map_consequence R w n ha rfn phi hr

theorem area_change_word (rfn : RelKey → Option Word) (u v : Word) (n : Nat)
    (ha : HasAreaWith rfn u n) (he : FreeGroup.mk u=FreeGroup.mk v) : HasAreaWith rfn v n := by
  obtain ⟨fs,hf,hv,hw⟩ := ha
  exact ⟨fs,hf,hv,hw.trans he⟩

end
end Blueprint.SV

#print axioms Blueprint.SV.ValidRelator
#print axioms Blueprint.SV.relatorValue
#print axioms Blueprint.SV.relationMap
#print axioms Blueprint.SV.relation_trivial
#print axioms Blueprint.SV.group_word_eval
#print axioms Blueprint.SV.area_of_quotient
#print axioms Blueprint.SV.area_map_consequence
#print axioms Blueprint.SV.map_area
#print axioms Blueprint.SV.area_change_word
