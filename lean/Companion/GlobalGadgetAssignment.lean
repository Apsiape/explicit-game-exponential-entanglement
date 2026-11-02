import Companion.GeneralGadgetPresentation
import Companion.StageValues
import Companion.ScalarPhase

namespace Companion.GeneralGadget
noncomputable section
open DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

def firstStage (p : Input) (phi : FreeGroup (Source p) →* U α) : Host p → U (Bool × α)
  | .inl a => diag (phi (srcOld a)) 1
  | .inr (.inl a) => swap α
  | .inr (.inr (.inl a)) => anti (phi (srcY a))⁻¹ (phi (srcY a))
  | .inr (.inr (.inr (.inl i))) =>
    diag 1 (phi (srcY (p.yIndex i))*phi (srcOld (p.c1[i]).1)*(phi (srcY (p.yIndex i)))⁻¹)
  | .inr (.inr (.inr (.inr false))) => swap α
  | .inr (.inr (.inr (.inr true))) => diag 1 (ScalarPhase.minusOne α)

def thirdStage (p : Input) (gamma : Host p → U α) : Nice p → U (Bool × α)
  | .inl (k,a) => if k=0 then diag (gamma a) (gamma a) else
    if k=1 then diag (gamma a) 1 else if k=2 then diag 1 (gamma a) else anti (gamma a) (gamma a)
  | .inr (.inl _) => swap α
  | .inr (.inr (t,b)) => let (_,y,z) := hostTriple p t
    if b then diag (gamma z) (gamma y) else diag (gamma y) (gamma z)

def fourthStage (p : Input) (gamma : Nice p → U α) : Variable p → U (Bool × α)
  | .inl a => diag (gamma a) (gamma a)
  | .inr (t,k) => let (a,b,c) := niceTriple p t
    StageValues.stage4 (gamma a) (gamma b) (gamma c) (FreeGroup.of (k.val+4))

abbrev Amplified (α : Type) := Bool × (Bool × (Bool × α))
def globalAssignment (p : Input) (phi : FreeGroup (Source p) →* U α) : Variable p → U (Amplified α) :=
  fourthStage p (thirdStage p (firstStage p phi))
def globalHom (p : Input) (phi : FreeGroup (Source p) →* U α) :
    FreeGroup (Option (Variable p)) →* U (Amplified α) :=
  FreeGroup.lift (fun v => v.elim (ScalarPhase.minusOne (Amplified α)) (globalAssignment p phi))

theorem amplified_card : Fintype.card (Amplified α)=8*Fintype.card α := by
  simp [Amplified]; omega
theorem global_J (p : Input) (phi : FreeGroup (Source p) →* U α) :
    (globalHom p phi (FreeGroup.of none):Matrix (Amplified α) (Amplified α) ℂ)=-1 := by
  simp [globalHom,ScalarPhase.minusOne,Option.elim_none]
theorem global_J_square (p : Input) (phi : FreeGroup (Source p) →* U α) :
    globalHom p phi (FreeGroup.of none)*globalHom p phi (FreeGroup.of none)=1 := by
  simpa [globalHom,Option.elim_none] using (ScalarPhase.square (α:=Amplified α))
theorem global_J_central (p : Input) (phi : FreeGroup (Source p) →* U α)
    (w : FreeGroup (Option (Variable p))) : Commute (globalHom p phi w) (globalHom p phi (FreeGroup.of none)) := by
  simpa [globalHom,Option.elim_none] using ScalarPhase.central (globalHom p phi w)

theorem step2_conjugacy (p : Input) (phi : FreeGroup (Source p) →* U α)
    (hw : phi (srcOld p.distinguished)=ScalarPhase.minusOne α) :
    firstStage p phi (hT p)*firstStage p phi (hOld p.distinguished)*firstStage p phi (hT p)=
      firstStage p phi (hU p) := by
  simpa [firstStage,hT,hU,hOld,hw] using (ScalarPhase.switch (α:=α))
theorem step2_linear (p : Input) (phi : FreeGroup (Source p) →* U α)
    (hw : phi (srcOld p.distinguished)=ScalarPhase.minusOne α) :
    ScalarPhase.minusOne (Bool × α)*
      (firstStage p phi (hOld p.distinguished)*firstStage p phi (hU p))=1 := by
  simp only [firstStage,hOld,hU,hw]
  rw [ScalarPhase.diagonal_product,ScalarPhase.square]

end
end Companion.GeneralGadget
