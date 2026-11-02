import Companion.DerivationChunk00
import Companion.DerivationChunk01
import Companion.DerivationChunk02
namespace Companion
def pauliRelators : List Word := [[(1, true), (2, true), (1, false), (2, false), (1, true), (2, true), (1, false), (2, false)], [(1, true), (2, true), (1, false), (2, false), (1, true), (1, true), (2, true), (1, false), (2, false), (1, false), (1, true), (2, true), (1, false), (2, false), (1, true), (1, true), (2, true), (1, false), (2, false), (1, false), (1, true), (2, true), (1, false), (2, false), (1, true), (1, true), (2, true), (1, false), (2, false), (1, false)], [(1, true), (2, true), (1, false), (2, false), (1, true), (1, true), (1, true), (2, true), (1, false), (2, false), (1, false), (1, false), (2, true), (1, true), (2, false), (1, false), (1, true), (1, true), (2, true), (1, true), (2, false), (1, false), (1, false), (1, false)], [(1, true), (1, true), (2, true), (1, false), (2, false), (1, false), (2, true), (2, true), (1, true), (2, false), (1, false), (2, false)], [(3, true), (3, true)], [(3, true), (1, true), (2, true), (1, false), (2, false), (1, true), (3, false), (1, false), (2, true), (1, true), (2, false), (1, false)], [(3, true), (1, true), (2, true), (1, false), (2, false), (2, true), (3, false), (2, false), (2, true), (1, true), (2, false), (1, false)], [(4, true), (1, true), (1, true), (2, true), (1, false), (2, false), (1, false), (1, true), (2, true), (1, false), (2, false), (1, true), (4, false), (1, false), (2, true), (1, true), (2, false), (1, false), (1, true), (2, true), (1, true), (2, false), (1, false), (1, false)], [(4, true), (1, true), (1, true), (2, true), (1, false), (2, false), (1, false), (1, true), (2, true), (1, false), (2, false), (2, true), (4, false), (2, false), (2, true), (1, true), (2, false), (1, false), (1, true), (2, true), (1, true), (2, false), (1, false), (1, false)], [(3, true), (1, true), (3, true), (1, false), (3, false), (1, true), (3, false), (1, false)], [(4, true), (3, true), (4, false), (1, true), (3, false), (1, false), (3, false)], [(4, true), (1, true), (3, true), (1, false), (4, false), (1, true), (3, false), (1, false)], [(4, true), (1, true), (1, true), (3, true), (1, false), (1, false), (4, false), (1, true), (1, true), (3, false), (1, false), (1, false)], [(1, true), (5, true), (1, false), (5, false)], [(1, true), (6, true), (1, false), (6, false)], [(2, true), (5, true), (2, false), (5, false)], [(2, true), (6, true), (2, false), (6, false)], [(4, true), (5, true), (4, false), (5, false)], [(4, true), (6, true), (4, false), (6, false)], [(5, true), (5, true)], [(6, true), (6, true)], [(5, true), (6, true), (5, true), (6, true), (5, true), (6, true), (5, true), (6, true)], [(5, true), (3, true), (5, true), (3, false), (5, false), (3, true), (5, false), (3, false)], [(5, true), (3, true), (6, true), (3, false), (5, false), (3, true), (6, false), (3, false)], [(6, true), (3, true), (5, true), (3, false), (6, false), (3, true), (5, false), (3, false)], [(6, true), (3, true), (6, true), (3, false), (6, false), (3, true), (6, false), (3, false)], [(5, true), (6, true), (5, true), (6, true), (3, true), (6, false), (5, false), (6, false), (5, false), (3, false)]]
def thetaLetter (a : Nat × Bool) : Word :=
  let w : Word := match a.1 with
    | 1 => [(27,true)]
    | 2 => [(1,true),(27,true),(1,true)]
    | 3 => [(2,true)]
    | 4 => [(3,true)]
    | 5 => [(4,true)]
    | 6 => [(5,true)]
    | _ => []
  if a.2 then w else FreeGroup.invRev w
def thetaWord (w : Word) : Word := w.flatMap thetaLetter
def derivationTargets : List Word := [derivationTarget01, derivationTarget02, derivationTarget03, derivationTarget04, derivationTarget05, derivationTarget06, derivationTarget07, derivationTarget08, derivationTarget09, derivationTarget10, derivationTarget11, derivationTarget12, derivationTarget13, derivationTarget14, derivationTarget15, derivationTarget16, derivationTarget17, derivationTarget18, derivationTarget19, derivationTarget20, derivationTarget21, derivationTarget22, derivationTarget23, derivationTarget24, derivationTarget25, derivationTarget26, derivationTarget27]
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem derivations_match : derivationTargets = pauliRelators.map thetaWord := by decide
theorem derivations_area : ∀ t ∈ derivationTargets, HasAreaWith (presentationRelator inputPresentation) t 60 := by
  intro t h
  simp only [derivationTargets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact derivationArea01
  · exact derivationArea02
  · exact derivationArea03
  · exact derivationArea04
  · exact derivationArea05
  · exact derivationArea06
  · exact derivationArea07
  · exact derivationArea08
  · exact derivationArea09
  · exact derivationArea10
  · exact derivationArea11
  · exact derivationArea12
  · exact derivationArea13
  · exact derivationArea14
  · exact derivationArea15
  · exact derivationArea16
  · exact derivationArea17
  · exact derivationArea18
  · exact derivationArea19
  · exact derivationArea20
  · exact derivationArea21
  · exact derivationArea22
  · exact derivationArea23
  · exact derivationArea24
  · exact derivationArea25
  · exact derivationArea26
  · exact derivationArea27
theorem pauli_derivations : ∀ w ∈ pauliRelators,
    HasAreaWith (presentationRelator inputPresentation) (thetaWord w) 60 := by
  intro w hw
  apply derivations_area
  rw [derivations_match]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩
end Companion
