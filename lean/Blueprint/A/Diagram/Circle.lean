import Blueprint.A.Diagram.Restriction
import Blueprint.A.Diagram.Specification
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
structure Circle (u : Word) where
  partner : Equiv.Perm (Fin u.length)
  involutive : Function.Involutive partner
  fixed_free : ∀ i, partner i ≠ i
  compatible : ∀ i, u.get (partner i) = inverse (u.get i)
  genusZero : MapEuler.GenusZero (finRotate u.length) partner
private def leftEquiv {A B : Type} : {x : A ⊕ B // x.isLeft} ≃ A where
  toFun x := x.val.getLeft x.property
  invFun x := ⟨Sum.inl x,rfl⟩
  left_inv x := Subtype.ext (Sum.inl_getLeft x.val x.property)
  right_inv _ := rfl
/-- An isolated exterior is restricted as an actual union of components;
Euler equality is derived using upper bounds on both complementary pieces. -/
theorem restrict_outer (u : Word) (ws : List Word)
    (d : WordBlocks.Matching inverse (u :: ws))
    (hi : ∀ i : Fin u.length, ∃ j : Fin u.length,
      d.partner (Sum.inl i) = Sum.inl j) : Nonempty (Circle u) := by
  classical
  let σ := BlockBoundary.rotation (WordBlocks.lengths (u :: ws))
  let α := d.partner
  let P : WordBlocks.Occ (u :: ws) → Prop := fun x => x.isLeft
  have hs : ∀ x, P (σ x) ↔ P x := by intro x; cases x <;> rfl
  have ha : ∀ x, P (α x) ↔ P x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i,he⟩ := Sum.isLeft_iff.mp hx
      obtain ⟨j,hj⟩ := hi i
      apply Sum.isLeft_iff.mpr
      refine ⟨j,?_⟩
      exact ((d.involutive x).symm.trans (congrArg α he)).trans hj
    · intro hx
      obtain ⟨i,rfl⟩ := Sum.isLeft_iff.mp hx
      obtain ⟨j,hj⟩ := hi i
      exact Sum.isLeft_iff.mpr ⟨j,hj⟩
  let e : Subtype P ≃ Fin u.length := leftEquiv
  let a := MapRestrict.perm α P ha
  have hz := MapConjugation.genusZero e _ _
    (MapRestrict.genusZero σ α P hs ha d.involutive d.genusZero)
  have hrot : e.permCongr (MapRestrict.perm σ P hs) = finRotate u.length := by ext i; rfl
  rw [hrot] at hz
  refine ⟨⟨e.permCongr a,PermutationTransport.involutive e a
    (MapRestrict.perm_involutive α P ha d.involutive),?_,?_,hz⟩⟩
  · apply PermutationTransport.fixed_free
    intro x hx
    exact d.fixed_free x.val (congrArg Subtype.val hx)
  · intro i
    obtain ⟨j,hj⟩ := hi i
    have hpair : (e.permCongr a) i = j := by
      change (α (Sum.inl i)).getLeft _ = j
      simp only [show α (Sum.inl i) = Sum.inl j from hj]
      rfl
    rw [hpair]
    simpa only [hj,WordBlocks.letter,Sum.elim_inl] using d.compatible (Sum.inl i)
/-- Convert the one-boundary coordinates back to literal word occurrences. -/
theorem Circle.to_matching {u : Word} (c : Circle u) :
    Nonempty (WordBlocks.Matching inverse [u]) := by
  let e : WordBlocks.Occ [u] ≃ Fin u.length := {
    toFun := fun x => match x with
      | Sum.inl i => i
      | Sum.inr i => Empty.elim i
    invFun := Sum.inl
    left_inv := by intro x; cases x with
      | inl i => rfl
      | inr i => exact Empty.elim i
    right_inv := fun _ => rfl }
  have hz := MapConjugation.genusZero e.symm _ _ c.genusZero
  have hrot : e.symm.permCongr (finRotate u.length) =
      BlockBoundary.rotation (WordBlocks.lengths [u]) := by
    ext x
    cases x with
    | inl i => rfl
    | inr i => exact Empty.elim i
  rw [hrot] at hz
  refine ⟨⟨e.symm.permCongr c.partner,
    PermutationTransport.involutive _ _ c.involutive,
    PermutationTransport.fixed_free _ _ c.fixed_free,?_,hz⟩⟩
  intro i
  cases i with
  | inl i =>
    have hp : (e.symm.permCongr c.partner) (Sum.inl i) = Sum.inl (c.partner i) := rfl
    simpa only [hp,WordBlocks.letter,Sum.elim_inl] using c.compatible i
  | inr i => exact Empty.elim i
end Blueprint.DiagramProof
