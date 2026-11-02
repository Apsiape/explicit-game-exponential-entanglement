import Blueprint.Definitions
import Mathlib.Analysis.InnerProductSpace.Completion

namespace Blueprint
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators TensorProduct
set_option maxHeartbeats 600000

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

abbrev SpatialTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] := UniformSpace.Completion (E ⊗[ℂ] F)

def positiveOperator (A : E →L[ℂ] E) : Prop :=
  (∀ x y, inner ℂ (A x) y=inner ℂ x (A y)) ∧ ∀ x, 0≤(inner ℂ x (A x)).re

def spatialWin (g : LCS) (psi : SpatialTensor E F)
    (A : Fin g.system.equations.length → (Fin g.system.n → Bool) → E →L[ℂ] E)
    (B : Fin g.system.n → Bool → F →L[ℂ] F) : ℝ :=
  ∑ i, ∑ j, g.pi i j * if j.val∈(g.system.equations[i.val]).vars then
    ∑ a, (inner ℂ psi (UniformSpace.Completion.map (TensorProduct.mapL (A i a) (B j (a j))) psi)).re else 1

def validSpatial (g : LCS)
    (A : Fin g.system.equations.length → (Fin g.system.n → Bool) → E →L[ℂ] E)
    (B : Fin g.system.n → Bool → F →L[ℂ] F) : Prop :=
  (∀ i a, positiveOperator (A i a)) ∧ (∀ i, ∑ a, A i a=ContinuousLinearMap.id ℂ E) ∧
  (∀ i a, ¬validAnswer g i a → A i a=0) ∧ (∀ j b, positiveOperator (B j b)) ∧
  (∀ j, B j true+B j false=ContinuousLinearMap.id ℂ F)

def NoSpatialPerfect (g : LCS) : Prop := ∀ (E F : Type)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (psi : SpatialTensor E F) A B, ‖psi‖=1 → validSpatial g A B → spatialWin g psi A B≠1

end
end Blueprint
