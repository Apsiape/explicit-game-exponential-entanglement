import Blueprint.A.PairPresentation

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof

/-- A homomorphism that fills each relator with one cell does not increase area. -/
theorem area_hom_one {α β ι κ : Type} (R : ι → FreeGroup α) (S : κ → FreeGroup β)
    (H : FreeGroup α →* FreeGroup β)
    (hR : ∀ i, FiniteArea.Area S (H (R i)) 1)
    {w : FreeGroup α} {k : Nat} (hw : FiniteArea.Area R w k) :
    FiniteArea.Area S (H w) k := by
  obtain ⟨fs,hfs,he⟩ := hw
  have hf (f : FiniteArea.Factor α ι) : FiniteArea.Area S (H (FiniteArea.factorValue R f)) 1 := by
    rcases f with ⟨g,i,b⟩
    cases b
    · simpa only [FiniteArea.factorValue,Bool.false_eq_true,↓reduceIte,map_mul,map_inv] using
        area_conj (H g) (area_inv (hR i))
    · simpa only [FiniteArea.factorValue,↓reduceIte,map_mul,map_inv] using area_conj (H g) (hR i)
  have hp : ∀ xs : List (FiniteArea.Factor α ι),
      FiniteArea.Area S (H ((xs.map (FiniteArea.factorValue R)).prod)) xs.length := by
    intro xs
    induction xs with
    | nil => simpa using area_one S 0
    | cons f xs ih =>
      simpa only [List.map_cons,List.prod_cons,map_mul,List.length_cons,Nat.add_comm] using area_mul (hf f) ih
  rw [←he]
  exact area_weaken (hp fs) hfs

def johnsonToH : FreeGroup (Fin 3) →* FreeGroup (Fin 2) := FreeGroup.lift fun i =>
  if i=0 then FreeGroup.of 0 else if i=1 then FreeGroup.of 1
  else groupComm (FreeGroup.of 0) (FreeGroup.of 1)

def houghtonToJ : FreeGroup (Fin 2) →* FreeGroup (Fin 3) :=
  FreeGroup.map fun i => ⟨i.val,by omega⟩

theorem johnson_relator_substitution (i : Fin 5) :
    johnsonToH (johnsonFiniteRelator i)=
      if i=3 then 1 else houghtonFiniteRelator ⟨if i.val<3 then i.val else 3,by split <;> omega⟩ := by
  fin_cases i <;> decide +kernel

theorem johnson_relators_area (i : Fin 5) :
    FiniteArea.Area houghtonFiniteRelator (johnsonToH (johnsonFiniteRelator i)) 1 := by
  rw [johnson_relator_substitution]
  split
  · exact area_one _ 1
  · exact ⟨[(1,⟨if i.val<3 then i.val else 3,by split <;> omega⟩,true)],by simp,
      by simp [FiniteArea.factorValue]⟩

theorem substitution_section : johnsonToH.comp houghtonToJ=MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> rfl

theorem point_section : johnsonFiniteHom.comp houghtonToJ=houghtonFiniteHom := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> rfl

/-- The Tietze substitution preserves the original input word length and cell bound. -/
theorem houghton_fills_of_johnson (n C : Nat) (hJ : Fills johnsonFiniteRelator johnsonFiniteHom n C) :
    Fills houghtonFiniteRelator houghtonFiniteHom n C := by
  intro w hw hn
  let v : List (Fin 3 × Bool) := w.map fun a => (⟨a.1.val,by have := a.1.isLt; omega⟩,a.2)
  have hv : FreeGroup.mk v=houghtonToJ (FreeGroup.mk w) := by
    rw [houghtonToJ,FreeGroup.map.mk]
  have hnJ : johnsonFiniteHom (FreeGroup.mk v)=1 := by
    rw [hv,←MonoidHom.comp_apply,point_section]
    exact hn
  have ha := hJ v (by simpa only [v,List.length_map] using hw) hnJ
  have h := area_hom_one johnsonFiniteRelator houghtonFiniteRelator johnsonToH johnson_relators_area ha
  rw [hv,←MonoidHom.comp_apply,substitution_section,MonoidHom.id_apply] at h
  exact h

theorem dehn_fills {α : Type} {r : Nat} (R : Fin r → FreeGroup α)
    (H : FreeGroup α →* Equiv.Perm Concrete.Point) (n : Nat) (h : ∃ C, Fills R H n C) :
    Fills R H n (dehn R H n) := by
  classical
  rw [dehn,dif_pos h]
  exact Nat.find_spec h

theorem dehn_le_filling {α : Type} {r : Nat} (R : Fin r → FreeGroup α)
    (H : FreeGroup α →* Equiv.Perm Concrete.Point) (n C : Nat) (h : Fills R H n C) :
    dehn R H n≤C := by
  classical
  rw [dehn,dif_pos ⟨C,h⟩]
  exact Nat.find_min' _ h

/-- Appendix A's presentation comparison, with the separate finiteness component explicit.
This does not assert either finiteness component or the quantitative Dehn bound. -/
theorem houghton_dehn_comparison (n : Nat)
    (hJ : ∃ C, Fills johnsonFiniteRelator johnsonFiniteHom n C) : dehnH n≤dehnJ n := by
  exact dehn_le_filling _ _ n (dehnJ n)
    (houghton_fills_of_johnson n (dehnJ n) (dehn_fills _ _ n hJ))

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.area_hom_one
#print axioms Blueprint.HoughtonProof.johnsonToH
#print axioms Blueprint.HoughtonProof.houghtonToJ
#print axioms Blueprint.HoughtonProof.johnson_relator_substitution
#print axioms Blueprint.HoughtonProof.johnson_relators_area
#print axioms Blueprint.HoughtonProof.substitution_section
#print axioms Blueprint.HoughtonProof.point_section
#print axioms Blueprint.HoughtonProof.houghton_fills_of_johnson
#print axioms Blueprint.HoughtonProof.dehn_fills
#print axioms Blueprint.HoughtonProof.dehn_le_filling
#print axioms Blueprint.HoughtonProof.houghton_dehn_comparison
