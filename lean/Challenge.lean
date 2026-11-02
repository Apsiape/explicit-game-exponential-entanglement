import Companion.Analytic
import Companion.Construction
import Companion.Derivations
import Companion.Gadget
import Companion.PresentationModel
import Companion.ReturnSpecification
import Companion.GeneralGadgetTheorem

/-! Statement boundary. Admitted challenge declarations below are never used
by the proof modules or `Audit.lean`. This file is the sole place for admissions.
The definitions imported here are transparent; the README maps them to the paper.
C1 and the model-validity half of C2 are stated using the concrete infinite
permutation model; their independent proofs are checked in Audit2. -/
namespace Challenge
open Companion

def C1 : Prop := pauliRelators.length=27 ∧
  ∀ w ∈ pauliRelators, Concrete.gpWordHom (FreeGroup.mk w)=1

def C2Model : Prop :=
  (∀ k w, presentationRelator inputPresentation k=some w →
    Concrete.presentationModelInGPplus (FreeGroup.mk w)=1) ∧
  Concrete.presentationModel (FreeGroup.of (inputPresentation.distinguished+1))=
    Concrete.wordPermutation true Concrete.jWord ∧
  Concrete.presentationModel (FreeGroup.of (inputPresentation.distinguished+1))≠1

def C3 : Prop := construct inputPresentation = suppliedGame ∧
  suppliedGame.n=1993 ∧ suppliedGame.equations.length=1687 ∧
  wellFormed suppliedGame=true ∧
  (suppliedGame.equations.filter (·.rhs)).length=1 ∧
  suppliedGame.equations.all (fun e => decide (e.vars.Pairwise (· < ·)))=true

def C4 : Prop :=
  (∀ t ∈ substitutedRelators inputPresentation, HasArea suppliedGame t 42) ∧
  HasArea suppliedGame (distinguishedCommutator inputPresentation) 42

def C2Derivations : Prop :=
  (∀ w ∈ pauliRelators, HasAreaWith (presentationRelator inputPresentation) (thetaWord w) 60) ∧
  HasAreaWith (presentationRelator inputPresentation) derivationTarget00 60 ∧
  HasAreaWith (presentationRelator inputPresentation) derivationTarget28 60

theorem c3 : C3 := by sorry
theorem c4 : C4 := by sorry
theorem c2Derivations : C2Derivations := by sorry
theorem sixEquationForcing : SixEquationForcing := by sorry

/-- General gadget lemma, with all G1--G3, counts and ordered binary rows.
The proof is supplied independently by GeneralGadget.gadgetLemma. -/
def GeneralGadget : Prop := Companion.GeneralGadget.Lemma
theorem generalGadget : GeneralGadget := by sorry

/-- NOT FORMALIZED: full finite-dimensional Theorem 4.1. -/
theorem count : Analytic.Count := by sorry
/-- NOT FORMALIZED: the uniform-error entropy conclusion, Corollary 4.2. -/
theorem uniformCount : Analytic.UniformCount := by sorry
/-- NOT FORMALIZED: finite-dimensional Theorem 5.1. -/
theorem transfer : Analytic.Transfer := by sorry
/-- NOT FORMALIZED: existence part of Theorem 5.4. See RESULT.md for omissions. -/
theorem returnExistence : Analytic.ReturnExistence := by sorry
/-- NOT FORMALIZED: full prescribed-measurement return theorem, including e=0. -/
theorem returnTheorem : Analytic.Return := by sorry
/-- NOT FORMALIZED: all three two-sided profile conclusions. -/
theorem twoSided : Analytic.TwoSided := by sorry

end Challenge
