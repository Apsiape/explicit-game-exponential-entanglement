import Companion.GeneralGadgetData
import Mathlib.Data.List.Nodup

namespace Companion.GeneralGadget

theorem nice_equation_nodup (p : Input) (e : BaseEquation p) : (niceEquation p e).vars.Nodup := by
  rcases e with i|e
  · apply (p.linear_nodup i).map
    intro a b h
    simpa [nOld,hOld] using h
  · rcases e with u|e
    · simp [niceEquation,nOld,hOld,hU]
    · rcases e with ⟨a,b⟩|⟨t,b⟩ <;> cases b <;>
        simp [niceEquation,nOld,nPrime,nDPrime,nBar,nG,nK]

theorem equation_nodup (p : Input) (e : EquationIndex p) : (systemEquation p e).vars.Nodup := by
  rcases e with i|⟨t,k⟩
  · exact (nice_equation_nodup p i).map Sum.inl_injective
  · fin_cases k <;> simp [systemEquation,old,lamp]

noncomputable def coefficient (p : Input) (e : EquationIndex p) (a : Variable p) : Bool := by
  classical
  exact decide (a ∈ (systemEquation p e).vars)

theorem coefficient_spec (p : Input) (e : EquationIndex p) (a : Variable p) :
    coefficient p e a=true ↔ a ∈ (systemEquation p e).vars := by
  simp [coefficient]

end Companion.GeneralGadget
