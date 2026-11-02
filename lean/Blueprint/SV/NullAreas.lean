import Blueprint.SV.KRelations

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic

abbrev FinalAlphabet := Option (GeneralGadget.Variable balancedInput)

def oldSource (j : Fin 13) : FreeGroup FinalAlphabet :=
  FreeGroup.of (some (GeneralGadget.old (GeneralGadget.nOld (GeneralGadget.hOld j))))

def kSourceHom : FreeGroup Nat →* FreeGroup FinalAlphabet :=
  FreeGroup.lift (kGroupAssignment oldSource)

def markerSource : FreeGroup FinalAlphabet :=
  FreeGroup.of (some (GeneralGadget.old (GeneralGadget.nOld (GeneralGadget.hT balancedInput))))

def freeCommutator {α : Type} (a b : FreeGroup α) : FreeGroup α := a*b*a⁻¹*b⁻¹

theorem source_canonical_evaluation :
    (PresentedGroup.mk (Set.range (GeneralGadget.orderedRelator balancedInput))).comp kSourceHom =
      FreeGroup.lift (kGroupAssignment (fun j : Fin 13 =>
        GeneralGadget.orderedX balancedInput
          (GeneralGadget.old (GeneralGadget.nOld (GeneralGadget.hOld j))))) := by
  apply FreeGroup.ext_hom
  intro j
  simp only [MonoidHom.comp_apply,kSourceHom,FreeGroup.lift_apply_of]
  unfold kGroupAssignment
  split <;> simp [oldSource,GeneralGadget.orderedX,PresentedGroup.of,map_mul]

/-- These are the exact finite-area inputs needed by the game pullback: K's
relators, the five centrality words, and the commutator marker. The witnesses
come from the proved quotient identities and normal-closure completeness. -/
theorem balanced_null_areas :
    (∀ r∈kRelators, ∃ n, FiniteArea.Area (GeneralGadget.orderedRelator balancedInput)
      (kSourceHom (FreeGroup.mk r)) n) ∧
    (∀ j : Nat, 1≤j → j≤5 → ∃ n, FiniteArea.Area (GeneralGadget.orderedRelator balancedInput)
      (kSourceHom (freeCommutator (FreeGroup.of j) (FreeGroup.of 3))) n) ∧
    ∃ n, FiniteArea.Area (GeneralGadget.orderedRelator balancedInput)
      (freeCommutator (kSourceHom (FreeGroup.of 3)) markerSource * FreeGroup.of none) n := by
  let H := PresentedGroup.mk (Set.range (GeneralGadget.orderedRelator balancedInput))
  let Q := fun j : Fin 13 => GeneralGadget.orderedX balancedInput
    (GeneralGadget.old (GeneralGadget.nOld (GeneralGadget.hOld j)))
  obtain ⟨hrel,hcentral,hmarker⟩ := solution_K_data
    (GeneralGadget.orderedX balancedInput) (GeneralGadget.orderedJ balancedInput)
      (GeneralGadget.ordered_canonical_solution balancedInput)
  have heval (w : FreeGroup Nat) : H (kSourceHom w) = FreeGroup.lift (kGroupAssignment Q) w :=
    DFunLike.congr_fun source_canonical_evaluation w
  constructor
  · intro r hr
    apply FiniteArea.exists_area_of_quotient
    exact (heval (FreeGroup.mk r)).trans (hrel r hr)
  constructor
  · intro j hj1 hj5
    apply FiniteArea.exists_area_of_quotient
    rw [heval]
    simp only [freeCommutator,map_mul,map_inv,FreeGroup.lift_apply_of]
    dsimp only [Q]
    rw [(hcentral j hj1 hj5).eq]
    group
  · apply FiniteArea.exists_area_of_quotient
    have hmark := (GeneralGadget.ordered_canonical_solution balancedInput).distinguished_relation
    change H (GeneralGadget.distinguishedWord balancedInput)=1 at hmark
    convert hmark using 1
    congr 1

end
end Blueprint.SV

#print axioms Blueprint.SV.FinalAlphabet
#print axioms Blueprint.SV.oldSource
#print axioms Blueprint.SV.kSourceHom
#print axioms Blueprint.SV.markerSource
#print axioms Blueprint.SV.freeCommutator
#print axioms Blueprint.SV.source_canonical_evaluation
#print axioms Blueprint.SV.balanced_null_areas
