import Blueprint.A.HashCocycleLaw

namespace Blueprint.AHash
noncomputable section
open Companion Concrete
open scoped Classical
set_option maxHeartbeats 600000

theorem registerDot_zero_left {α : Type} [Fintype α] (a : α → Bool) : registerDot 0 a=0 := by
  simp [registerDot]

theorem registerDot_zero_right {α : Type} [Fintype α] (a : α → Bool) : registerDot a 0=0 := by
  simp [registerDot]

theorem registerDot_comm {α : Type} [Fintype α] (a b : α → Bool) : registerDot a b=registerDot b a := by
  simp only [registerDot,mul_comm]

theorem registerDot_comp {α : Type} [Fintype α] (g : Equiv.Perm α) (a b : α → Bool) :
    registerDot (a ∘ g) (b ∘ g)=registerDot a b := by
  exact Equiv.sum_comp g (fun i => a i*b i)

/-- The exact, unhashed phase/register action of finite affine-and-lamp data. -/
def hashGammaAction {n : Nat} (x : HashGamma n) (s : Bool × ((Fin n → Bool) → Bool)) :
    Bool × ((Fin n → Bool) → Bool) :=
  (s.1+x.2.1+registerDot x.2.2.2 (s.2 ∘ x.1.symm), s.2 ∘ x.1.symm+x.2.2.1)

theorem hashGammaAction_one (n : Nat) (s : Bool × ((Fin n → Bool) → Bool)) :
    hashGammaAction (hashGammaOne n) s=s := by
  rcases s with ⟨c,q⟩
  apply Prod.ext
  · simp [hashGammaAction,hashGammaOne,registerDot_zero_left]
  · simp [hashGammaAction,hashGammaOne,←AffineEquiv.inv_def]

theorem hashGammaAction_mul {n : Nat} (x y : HashGamma n) (s : Bool × ((Fin n → Bool) → Bool)) :
    hashGammaAction (hashGammaMul x y) s=hashGammaAction x (hashGammaAction y s) := by
  have hc : (s.2 ∘ y.1.symm+y.2.2.1) ∘ x.1.symm=
      s.2 ∘ (x.1*y.1).symm+y.2.2.1 ∘ x.1.symm := rfl
  have hd : registerDot (y.2.2.2 ∘ x.1.symm) (s.2 ∘ (x.1*y.1).symm)=
      registerDot y.2.2.2 (s.2 ∘ y.1.symm) :=
    registerDot_comp x.1.symm.toEquiv y.2.2.2 (s.2 ∘ y.1.symm)
  apply Prod.ext
  · change s.1+(x.2.1+y.2.1+registerDot x.2.2.2 (y.2.2.1 ∘ x.1.symm))+
        registerDot (x.2.2.2+y.2.2.2 ∘ x.1.symm) (s.2 ∘ (x.1*y.1).symm)=
      (s.1+y.2.1+registerDot y.2.2.2 (s.2 ∘ y.1.symm))+x.2.1+
        registerDot x.2.2.2 ((s.2 ∘ y.1.symm+y.2.2.1) ∘ x.1.symm)
    rw [hc,registerDot_add_left,registerDot_add_right,hd]
    ring
  · change s.2 ∘ (x.1*y.1).symm+(x.2.2.1+y.2.2.1 ∘ x.1.symm)=
      (s.2 ∘ y.1.symm+y.2.2.1) ∘ x.1.symm+x.2.2.1
    rw [hc]
    ac_rfl

/-- The finite action recovers every affine map, lamp mask and central bit. -/
theorem hashGammaAction_faithful {n : Nat} (x : HashGamma n)
    (hx : ∀ s, hashGammaAction x s=s) : x=hashGammaOne n := by
  have hz := hx (0,0)
  have hs : x.2.1=0 := by
    have h := congrArg Prod.fst hz
    change 0+x.2.1+registerDot x.2.2.2 (0:((Fin n → Bool) → Bool))=0 at h
    simpa only [zero_add,registerDot_zero_right,add_zero] using h
  have ha : x.2.2.1=0 := by
    have h := congrArg Prod.snd hz
    change (0:((Fin n → Bool) → Bool))+x.2.2.1=0 at h
    simpa only [zero_add] using h
  have hgInv (v : Fin n → Bool) : x.1.symm v=v := by
    have h := congrFun (congrArg Prod.snd (hx (0,siteMask v))) v
    simp only [hashGammaAction,ha,add_zero,Function.comp_apply,siteMask] at h
    by_contra hn
    simp [hn] at h
  have hg : x.1=1 := by
    apply AffineEquiv.ext
    intro v
    have h := hgInv (x.1 v)
    simpa only [AffineEquiv.symm_apply_apply,AffineEquiv.coe_one,id_eq] using h.symm
  have hb : x.2.2.2=0 := by
    funext v
    change x.2.2.2 v=0
    have h := congrArg Prod.fst (hx (0,siteMask v))
    rw [hashGammaAction,hs,hg] at h
    change 0+0+registerDot x.2.2.2 (siteMask v)=0 at h
    rw [zero_add,registerDot_comm,registerDot_site] at h
    simpa only [zero_add] using h
  exact Prod.ext hg (Prod.ext hs (Prod.ext ha hb))

theorem hashGammaProduct_action {n : Nat} (xs : List (HashGamma n))
    (s : Bool × ((Fin n → Bool) → Bool)) :
    hashGammaAction (hashGammaProduct xs) s=xs.foldr hashGammaAction s := by
  induction xs with
  | nil => exact hashGammaAction_one n s
  | cons x xs ih => rw [hashGammaProduct,hashGammaAction_mul,ih]; rfl

end
end Blueprint.AHash

#print axioms Blueprint.AHash.registerDot_zero_left
#print axioms Blueprint.AHash.registerDot_zero_right
#print axioms Blueprint.AHash.registerDot_comm
#print axioms Blueprint.AHash.registerDot_comp
#print axioms Blueprint.AHash.hashGammaAction
#print axioms Blueprint.AHash.hashGammaAction_one
#print axioms Blueprint.AHash.hashGammaAction_mul
#print axioms Blueprint.AHash.hashGammaAction_faithful
#print axioms Blueprint.AHash.hashGammaProduct_action
