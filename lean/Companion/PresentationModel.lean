import Companion.GroupCertificates
import Companion.WordSubstitution
import Companion.Data
namespace Companion.Concrete
def definingImages : List Word := [[(7, true)], [(3, true)], [(4, true)], [(5, true)], [(6, true)], [(1, true), (7, true), (1, true), (7, true), (1, false), (7, false), (1, false), (7, false)], [(1, true), (7, true), (1, false)], [(1, true), (1, true), (7, true), (1, false), (1, false)], [(1, true), (7, true), (1, true), (7, true), (1, false), (7, true), (1, false)], [(1, true), (1, true), (7, true), (1, true), (7, true), (1, false), (7, false), (1, false), (7, false), (1, false)], [(1, true), (7, true), (1, true), (7, true), (1, false), (7, false), (1, false), (7, false), (1, true), (1, true), (7, true), (1, true), (7, true), (1, false), (1, false), (7, false), (1, false), (7, false)], [(1, true), (1, true), (1, true), (7, true), (1, true), (7, true), (1, false), (7, false), (1, false), (7, false), (1, false), (1, false)], [(1, true), (3, true), (1, false)], [(1, true), (4, true), (1, false)], [(1, true), (7, true), (1, true), (7, true), (1, false), (7, false), (1, false), (7, false), (1, true), (4, true), (7, true), (1, true), (7, true), (1, false), (7, false), (1, false), (7, false)], [(3, true), (1, true), (3, true), (1, false)], [(1, true), (1, true), (3, true), (1, false), (1, false)], [(5, true), (6, true), (5, true)], [(6, true), (5, true), (6, true)], [(5, true), (6, true), (5, true), (6, true)], [(5, true), (3, true), (5, true)], [(3, true), (5, true), (3, true)], [(5, true), (3, true), (5, true), (3, true)], [(3, true), (6, true), (3, true)], [(6, true), (3, true), (6, true)], [(6, true), (3, true), (6, true), (3, true)]]
def modelImages : Nat → Word
  | 0 => []
  | j+1 => if j=26 then [(1,true)] else definingImages[j]?.getD []
def sourceModelWords : List Word := (presentationWords inputPresentation).map (substituteWords modelImages)
def presentationModel : FreeGroup Nat →* Equiv.Perm Sample :=
  (wordHom true).comp (FreeGroup.lift (fun j => FreeGroup.mk (modelImages j)))
theorem presentationModel_word (w : Word) :
    presentationModel (FreeGroup.mk w) = wordPermutation true (substituteWords modelImages w) := by
  change wordHom true (FreeGroup.lift (fun j => FreeGroup.mk (modelImages j)) (FreeGroup.mk w)) = _
  rw [← mk_substituteWords]
  rfl
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem c2_model_checks : sourceModelWords.all (wordIdentityCheck true)=true := by decide +kernel
theorem source_presentation_format : inputPresentation.n0=26 ∧ inputPresentation.c0.length=76 ∧
    inputPresentation.c1.length=10 ∧ inputPresentation.linear.length=8 ∧
    inputPresentation.c0.all (fun (a,b,c) => decide (a<26 ∧ b<26 ∧ c<26))=true ∧
    inputPresentation.c1.all (fun (b,c) => decide (b<26 ∧ c<26))=true ∧
    inputPresentation.linear.all (fun vs => decide (vs.length=3 ∧ vs.Nodup) && vs.all (· < 26))=true := by decide +kernel
theorem source_linear_commutations : inputPresentation.linear.all (fun vs =>
    vs.all (fun a => vs.all (fun b => decide (a=b ∨ (a,b,b) ∈ inputPresentation.c0 ∨ (b,a,a) ∈ inputPresentation.c0))))=true := by decide +kernel
theorem source_relator_length : sourceModelWords.all (fun w => decide ((FreeGroup.reduce w).length≤44))=true := by decide +kernel
theorem c2_model_words : ∀ w ∈ presentationWords inputPresentation, presentationModel (FreeGroup.mk w)=1 := by
  intro w hw
  rw [presentationModel_word]
  apply wordIdentityCheck_sound
  apply List.all_eq_true.mp c2_model_checks
  exact List.mem_map.mpr ⟨w,hw,rfl⟩
theorem c2_model_relators (k : RelKey) (w : Word)
    (h : presentationRelator inputPresentation k=some w) : presentationModel (FreeGroup.mk w)=1 :=
  c2_model_words w (presentationRelator_mem h)
def presentationModelInGPplus : FreeGroup Nat →* GPplus :=
  gpPlusWordHom.comp (FreeGroup.lift (fun j => FreeGroup.mk (modelImages j)))
theorem c2_model_group (k : RelKey) (w : Word)
    (h : presentationRelator inputPresentation k=some w) : presentationModelInGPplus (FreeGroup.mk w)=1 := by
  apply Subtype.ext
  exact c2_model_relators k w h
theorem model_distinguished_word : modelImages (inputPresentation.distinguished+1)=jWord := by decide +kernel
theorem model_distinguished : presentationModel (FreeGroup.of (inputPresentation.distinguished+1))=wordPermutation true jWord := by
  simp only [presentationModel,MonoidHom.comp_apply,FreeGroup.lift_apply_of,wordPermutation]
  rw [model_distinguished_word]
theorem model_distinguished_nontrivial : presentationModel (FreeGroup.of (inputPresentation.distinguished+1))≠1 := by
  rw [model_distinguished]
  exact j_nontrivial true
end Companion.Concrete
