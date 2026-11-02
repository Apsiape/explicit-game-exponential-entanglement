import Blueprint.SV.NumericRelations
import Blueprint.ASector

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic

def numberedImages (j : Nat) : Word := (numberedHom (kSourceHom (FreeGroup.of j))).toWord
def numberedMarker : Word := (numberedHom markerSource).toWord

theorem numbered_substitute (w : Word) :
    FreeGroup.mk (substituteWords numberedImages w)=numberedHom (kSourceHom (FreeGroup.mk w)) := by
  rw [mk_substituteWords]
  have hh : FreeGroup.lift (fun j => FreeGroup.mk (numberedImages j))=numberedHom.comp kSourceHom := by
    apply FreeGroup.ext_hom
    intro j
    simp [numberedImages,MonoidHom.comp_apply,FreeGroup.mk_toWord]
  rw [hh]
  rfl

theorem mk_commWord (u v : Word) :
    FreeGroup.mk (ASector.commWord u v)=freeCommutator (FreeGroup.mk u) (FreeGroup.mk v) := by
  simp [ASector.commWord,freeCommutator,←FreeGroup.mul_mk,←FreeGroup.inv_mk,mul_assoc]

/-- The exact numeric finite-area certificates required by SVSpecification. -/
theorem numeric_area_data :
    ∃ images : Nat → Word, ∃ z : Word,
      (∀ r∈kRelators, ∃ k, HasArea numericGame.system (substituteWords images r) k) ∧
      (∀ j, 1≤j → j≤5 → ∃ k, HasArea numericGame.system
        (substituteWords images (ASector.commWord [(j,true)] [(3,true)])) k) ∧
      ∃ k, HasArea numericGame.system (ASector.commWord (images 3) z++[neg numericGame.system.n]) k := by
  refine ⟨numberedImages,numberedMarker,?_,?_,?_⟩
  · intro r hr
    obtain ⟨n,ha⟩ := balanced_null_areas.1 r hr
    obtain ⟨k,hk⟩ := map_area _ _ n ha (relator numericSystem) numberedHom numeric_ordered_trivial
    refine ⟨k,area_change_word (relator numericSystem) _ _ k hk ?_⟩
    rw [FreeGroup.mk_toWord,numbered_substitute]
  · intro j hj1 hj5
    obtain ⟨n,ha⟩ := balanced_null_areas.2.1 j hj1 hj5
    obtain ⟨k,hk⟩ := map_area _ _ n ha (relator numericSystem) numberedHom numeric_ordered_trivial
    refine ⟨k,area_change_word (relator numericSystem) _ _ k hk ?_⟩
    rw [FreeGroup.mk_toWord,numbered_substitute,mk_commWord]
    rfl
  · apply area_of_quotient (relator numericSystem)
    let H := relationMap (relator numericSystem)
    obtain ⟨n,ha⟩ := balanced_null_areas.2.2
    have hplus := area_map_consequence _ _ n ha (relator numericSystem) numberedHom numeric_ordered_trivial
    have hJinv : (H (FreeGroup.of 407))⁻¹=H (FreeGroup.of 407) :=
      inv_eq_of_mul_eq_one_left numeric_J_square
    rw [←FreeGroup.mul_mk,mk_commWord]
    simp only [numberedImages,numberedMarker,FreeGroup.mk_toWord]
    change H (freeCommutator (numberedHom (kSourceHom (FreeGroup.of 3)))
      (numberedHom markerSource) * (FreeGroup.of 407)⁻¹)=1
    have hnumJ : numberedHom (FreeGroup.of none)=FreeGroup.of 407 := by
      simp [numberedHom,numberedLetter]
    simp only [freeCommutator,map_mul,map_inv,hnumJ] at hplus ⊢
    rw [hJinv]
    exact hplus

end
end Blueprint.SV

#print axioms Blueprint.SV.numberedImages
#print axioms Blueprint.SV.numberedMarker
#print axioms Blueprint.SV.numbered_substitute
#print axioms Blueprint.SV.mk_commWord
#print axioms Blueprint.SV.numeric_area_data
