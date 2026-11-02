import Blueprint.A.OmegaPermutation
import Mathlib.GroupTheory.Perm.ViaEmbedding

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def shiftPoint (k : Nat) : Concrete.Point ↪ Concrete.Point where
  toFun y := (y.1,if y.1=Concrete.Ray.one then y.2+k else y.2)
  inj' := by
    rintro ⟨r,h⟩ ⟨s,j⟩ he
    have hr := congrArg Prod.fst he
    dsimp at hr
    subst s
    have hh := congrArg Prod.snd he
    dsimp at hh
    cases r <;> simp_all

def shiftHom (k : Nat) : Equiv.Perm Concrete.Point →* Equiv.Perm Concrete.Point :=
  Equiv.Perm.viaEmbeddingHom (shiftPoint k)

theorem shiftHom_apply (k : Nat) (g : Equiv.Perm Concrete.Point) (y : Concrete.Point) :
    shiftHom k g (shiftPoint k y)=shiftPoint k (g y) :=
  Equiv.Perm.viaEmbedding_apply g (shiftPoint k) y

theorem shiftHom_low (k h : Nat) (g : Equiv.Perm Concrete.Point) (hh : h<k) :
    shiftHom k g (Concrete.Ray.one,h)=(Concrete.Ray.one,h) := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨⟨r,j⟩,he⟩
  have hr := congrArg Prod.fst he
  change r=Concrete.Ray.one at hr
  subst r
  have hj := congrArg Prod.snd he
  change j+k=h at hj
  omega

theorem shiftHom_swap (k i j : Nat) :
    shiftHom k (Equiv.swap (Concrete.Ray.one,i) (Concrete.Ray.one,j))=
      Equiv.swap (Concrete.Ray.one,i+k) (Concrete.Ray.one,j+k) := by
  apply Equiv.ext
  intro y
  by_cases hr : y∈Set.range (shiftPoint k)
  · obtain ⟨z,rfl⟩ := hr
    rw [shiftHom_apply]
    have hi : shiftPoint k z=(Concrete.Ray.one,i+k) ↔ z=(Concrete.Ray.one,i) :=
      by change shiftPoint k z=shiftPoint k (Concrete.Ray.one,i) ↔ _; exact (shiftPoint k).injective.eq_iff
    have hj : shiftPoint k z=(Concrete.Ray.one,j+k) ↔ z=(Concrete.Ray.one,j) :=
      by change shiftPoint k z=shiftPoint k (Concrete.Ray.one,j) ↔ _; exact (shiftPoint k).injective.eq_iff
    by_cases hzi : z=(Concrete.Ray.one,i)
    · subst z
      change shiftPoint k (Equiv.swap _ _ (Concrete.Ray.one,i))=
        Equiv.swap (Concrete.Ray.one,i+k) (Concrete.Ray.one,j+k) (Concrete.Ray.one,i+k)
      rw [Equiv.swap_apply_left,Equiv.swap_apply_left]
      rfl
    by_cases hzj : z=(Concrete.Ray.one,j)
    · subst z
      change shiftPoint k (Equiv.swap _ _ (Concrete.Ray.one,j))=
        Equiv.swap (Concrete.Ray.one,i+k) (Concrete.Ray.one,j+k) (Concrete.Ray.one,j+k)
      rw [Equiv.swap_apply_right,Equiv.swap_apply_right]
      rfl
    rw [Equiv.swap_apply_of_ne_of_ne hzi hzj]
    exact (Equiv.swap_apply_of_ne_of_ne (fun he => hzi (hi.mp he)) (fun he => hzj (hj.mp he))).symm
  · rw [show shiftHom k _ y=y from Equiv.Perm.viaEmbedding_apply_of_notMem _ _ y hr]
    apply (Equiv.swap_apply_of_ne_of_ne _ _).symm
    · intro he; apply hr; exact ⟨(Concrete.Ray.one,i),he.symm⟩
    · intro he; apply hr; exact ⟨(Concrete.Ray.one,j),he.symm⟩

def stabilizerWord (k j : Nat) : Word :=
  (if k=1 then [(1,true),(2,true),(1,false),(2,false)] else
    [(1,true),(1,true),(2,true),(1,false),(2,false),(1,false),
      (1,true),(2,true),(1,false),(2,false)]) ++ [(j,true)]

theorem shiftHom_other (k : Nat) (g : Equiv.Perm Concrete.Point) (r : Concrete.Ray) (h : Nat)
    (hr : r≠Concrete.Ray.one) :
    shiftHom k g (r,h)=shiftPoint k (g (r,h)) := by
  have he : shiftPoint k (r,h)=(r,h) := by simp [shiftPoint,hr]
  simpa only [he] using shiftHom_apply k g (r,h)

theorem shiftHom_generators (k : Nat) (hk : k=1 ∨ k=2) (j : Nat) (hj : j=1 ∨ j=2) :
    shiftHom k (pointHom (FreeGroup.of j))=pointHom (FreeGroup.mk (stabilizerWord k j)) := by
  rcases hk with rfl|rfl
  · rcases hj with rfl|rfl
    all_goals
      apply Equiv.ext
      rintro ⟨r,h⟩
      cases r with
      | one =>
        cases h with
        | zero => rw [shiftHom_low 1 0 _ (by decide)]; rfl
        | succ h =>
          change shiftHom 1 _ (shiftPoint 1 (Concrete.Ray.one,h))=_
          rw [shiftHom_apply]
          rfl
      | two => rw [shiftHom_other 1 _ _ _ (by decide)]; cases h <;> rfl
      | three => rw [shiftHom_other 1 _ _ _ (by decide)]; cases h <;> rfl
  · rcases hj with rfl|rfl
    all_goals
      apply Equiv.ext
      rintro ⟨r,h⟩
      cases r with
      | one =>
        rcases h with _|_|h
        · rw [shiftHom_low 2 0 _ (by decide)]; rfl
        · rw [shiftHom_low 2 1 _ (by decide)]; rfl
        · change shiftHom 2 _ (shiftPoint 2 (Concrete.Ray.one,h))=_
          rw [shiftHom_apply]
          rfl
      | two => rw [shiftHom_other 2 _ _ _ (by decide)]; cases h <;> rfl
      | three => rw [shiftHom_other 2 _ _ _ (by decide)]; cases h <;> rfl

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.shiftPoint
#print axioms Blueprint.PairProof.shiftHom
#print axioms Blueprint.PairProof.shiftHom_apply
#print axioms Blueprint.PairProof.shiftHom_low
#print axioms Blueprint.PairProof.shiftHom_swap
#print axioms Blueprint.PairProof.stabilizerWord
#print axioms Blueprint.PairProof.shiftHom_other
#print axioms Blueprint.PairProof.shiftHom_generators
