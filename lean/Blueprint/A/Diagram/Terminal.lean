import Blueprint.A.Diagram.Initial
import Blueprint.A.Diagram.Circle
import Blueprint.A.Diagram.EulerEar
import Blueprint.A.Diagram.BoundaryReduction
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
/-- A nonempty cyclically reduced word cannot bound a one-vertex sphere map:
Euler forces an adjacent inverse pair in the doubled boundary word. -/
theorem cyclic_empty (u : Word) (c : Circle u) (h : FreeGroup.IsCyclicallyReduced u) :
    u = [] := by
  classical
  by_contra hn
  have hp : 0 < u.length := List.length_pos_iff.mpr hn
  let : Nonempty (Fin u.length) := ⟨⟨0,hp⟩⟩
  have ht : ∀ x y : Fin u.length, (finRotate u.length).SameCycle x y := by
    intro x y
    by_cases hlen : u.length = 1
    · have he : x = y := Fin.ext (by have hx := x.isLt; have hy := y.isLt; omega)
      subst y
      exact Equiv.Perm.SameCycle.refl _ _
    · exact WordPairing.rotate_sameCycle (by omega) x y
  obtain ⟨i,hi⟩ := euler_ear (finRotate u.length) c.partner c.fixed_free ht c.genusZero
  have he : c.partner i = finRotate u.length i := by
    have hh : c.partner (finRotate u.length i) = i := hi
    exact (congrArg c.partner hh).symm.trans (c.involutive _)
  have hl := c.compatible i
  rw [he] at hl
  have hh : FreeGroup.IsReduced (u ++ u) := by
    simpa only [List.replicate_succ,List.replicate_zero,List.flatten_cons,
      List.flatten_nil,List.append_nil] using (h.flatten_replicate 2).isReduced
  have hbound : i.val + 1 < (u ++ u).length := by
    have hb := i.isLt
    simp only [List.length_append]
    omega
  have hrel := (List.isChain_iff_getElem.mp hh) i.val hbound
  have hfirst : (u ++ u)[i.val] = u.get i := by
    simp only [List.get_eq_getElem,List.getElem_append_left i.isLt]
  have hnext : (u ++ u)[i.val+1] = u.get (finRotate u.length i) := by
    by_cases hlt : i.val + 1 < u.length
    · have hr : (finRotate u.length i).val = i.val+1 := by
        rw [ContiguousSplit.rotate_val,ite_eq_right (by omega)]
      simp only [List.get_eq_getElem,hr,List.getElem_append_left hlt]
    · have hx : i.val+1 = u.length := by have hb := i.isLt; omega
      have hr : (finRotate u.length i).val = 0 := by
        rw [ContiguousSplit.rotate_val,ite_eq_left hx]
      simp only [List.get_eq_getElem,hr,hx]
      simpa only [Nat.zero_add] using (List.getElem_append_right' u hp).symm
  rw [hfirst,hnext,hl] at hrel
  have hb := hrel (by rfl)
  cases hbit : (u.get i).2 <;> simp [inverse] at hb
/-- The no-face boundary is freely trivial, derived from a real finite map. -/
theorem single_trivial (u : Word) (d : WordBlocks.Matching inverse [u]) :
    FreeGroup.mk u = 1 := by
  obtain ⟨s⟩ := reduce_matching (FreeGroup.reduce.red (L := u)) [] d
  let v := FreeGroup.reduce u
  let c := FreeGroup.reduceCyclically v
  let a := FreeGroup.reduceCyclically.conjugator v
  have hs : a ++ c ++ FreeGroup.invRev a = v :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically v
  obtain ⟨t⟩ := remove_conjugator a c [] (by simpa only [hs] using s)
  obtain ⟨cc⟩ := restrict_outer c [] t (by
    intro i
    cases hj : t.partner (Sum.inl i) with
    | inl j => exact ⟨j,rfl⟩
    | inr j => exact Empty.elim j)
  have hc : c = [] := cyclic_empty c cc
    (FreeGroup.reduceCyclically.isCyclicallyReduced
      (FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem))
  have hm := congrArg (FreeGroup.mk (α := Nat)) hs
  simpa only [hc,List.append_nil,←FreeGroup.mul_mk,←FreeGroup.inv_mk,
    mul_inv_cancel,v,FreeGroup.reduce.self] using hm.symm
end Blueprint.DiagramProof
