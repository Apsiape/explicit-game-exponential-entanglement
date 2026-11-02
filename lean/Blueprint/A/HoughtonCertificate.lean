import Blueprint.A.HoughtonCorollary
import Blueprint.A.LocalBasic

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published HoughtonProof

theorem houghton_certificate_relator (i : Fin 4) :
    FreeGroup.map (fun j : Fin 2 => j.val+1) (houghtonFiniteRelator i)=sourceRelator ⟨i.val,by
      have := i.isLt; change i.val<27; omega⟩ := by
  fin_cases i <;> decide +kernel

/-- The proved Houghton Dehn function supplies actual cells of the fixed
Pauli certificate for every null p,q word. -/
theorem houghton_certificate_area (w : Word) (N : Nat) (hN : 1≤N)
    (hw : w.length≤N) (ha : ∀ a∈w, a.1∈[1,2]) (hn : pointHom (FreeGroup.mk w)=1) :
    FiniteArea.Area sourceRelator (FreeGroup.mk w) (dehnH N) := by
  let f := fun j : Nat => (⟨(j-1)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)
  let v : List (Fin 2 × Bool) := w.map fun a => (f a.1,a.2)
  let H := FreeGroup.map (fun j : Fin 2 => j.val+1)
  have he : H (FreeGroup.mk v)=FreeGroup.mk w := by
    simp only [H,v,FreeGroup.map.mk,List.map_map,Function.comp_def]
    congr 1
    conv_rhs => rw [←List.map_id w]
    apply List.map_congr_left
    intro a ha'
    have hh := ha a ha'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with hh|hh <;> cases a with | mk j b => cases hh; rfl
  have hp : houghtonFiniteHom (FreeGroup.mk v)=1 := by
    change pointHom (H (FreeGroup.mk v))=1
    rw [he,hn]
  have hv := dehn_fills houghtonFiniteRelator houghtonFiniteHom N (houghtonDehnCorollary N hN).1 v
    (by simpa only [v,List.length_map] using hw) hp
  have hc (i : Fin 4) : FiniteArea.Area sourceRelator (H (houghtonFiniteRelator i)) 1 := by
    rw [houghton_certificate_relator]
    exact source_area _
  have hh := area_hom_one houghtonFiniteRelator sourceRelator H hc hv
  rw [he] at hh
  exact hh

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.houghton_certificate_relator
#print axioms Blueprint.PairProof.houghton_certificate_area
