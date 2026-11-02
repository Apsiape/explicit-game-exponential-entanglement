import Blueprint.A.Diagram.Specification
import Blueprint.A.Diagram.BoundaryReduction
namespace Blueprint.DiagramProof
open scoped Classical
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
noncomputable section
namespace MergeChart
/-- A literal cyclic cut, with an explicit occurrence equivalence. -/
def cut (a b : Word) : Fin (a ++ b).length ≃ Fin (b ++ a).length :=
  (finCongr (List.length_append (as := a) (bs := b))).trans
    (finAddFlip.trans (finCongr (List.length_append (as := b) (bs := a)).symm))
lemma cut_val (a b : Word) (i : Fin (a ++ b).length) :
    (cut a b i).val = if i.val < a.length then b.length + i.val else i.val - a.length := by
  change (finAddFlip (⟨i.val, _⟩ : Fin (a.length+b.length))).val = _
  by_cases h : i.val < a.length
  · rw [finAddFlip_apply_mk_left h,ite_eq_left h]
  · rw [finAddFlip_apply_mk_right (Nat.le_of_not_gt h),ite_eq_right h]
lemma cut_letter (a b : Word) (i : Fin (a ++ b).length) :
    (b ++ a).get (cut a b i) = (a ++ b).get i := by
  simp only [List.get_eq_getElem,cut_val]
  by_cases h : i.val < a.length
  · simp only [ite_eq_left h,List.getElem_append_left h]
    simpa only [Nat.add_comm] using (List.getElem_append_right' b h).symm
  · simp only [ite_eq_right h,List.getElem_append_right (Nat.le_of_not_gt h)]
    rw [List.getElem_append_left (by have hi:=i.isLt; simp only [List.length_append] at hi; omega)]
lemma cut_rotation (a b : Word) (i : Fin (a ++ b).length) :
    cut a b (finRotate _ i) = finRotate _ (cut a b i) := by
  apply Fin.ext
  simp only [cut_val,ContiguousSplit.rotate_val,List.length_append]
  have hi:=i.isLt
  simp only [List.length_append] at hi
  split_ifs <;> omega

def cutBlocks (a b : Word) (ws : List Word) :
    WordBlocks.Occ ((a ++ b) :: ws) ≃ WordBlocks.Occ ((b ++ a) :: ws) :=
  Equiv.sumCongr (cut a b) (Equiv.refl _)
def cutMatching (a b : Word) (ws : List Word)
    (d : WordBlocks.Matching inverse ((a ++ b) :: ws)) :
    WordBlocks.Matching inverse ((b ++ a) :: ws) :=
  d.rename (cutBlocks a b ws)
    (fun x => by cases x with | inl i => exact cut_letter a b i | inr i => rfl)
    (fun x => by cases x with | inl i => exact congrArg Sum.inl (cut_rotation a b i) | inr i => rfl)
section Numeric
variable {R : Type} (n m : Nat)
abbrev Old := Fin (n+1) ⊕ (Fin (m+1) ⊕ R)
abbrev first : Old (R:=R) n m := .inl (Fin.last n)
abbrev second : Old (R:=R) n m := .inr (.inl (Fin.last m))
lemma different : first (R:=R) n m ≠ second n m := by intro h; cases h

def lift : Fin (n+m) ⊕ R → Old (R:=R) n m
  | .inl i => if h : i.val < n then .inl ⟨i.val,by omega⟩
      else .inr (.inl ⟨i.val-n,by have hh:=i.isLt; omega⟩)
  | .inr r => .inr (.inr r)
lemma lift_ne (x : Fin (n+m) ⊕ R) :
    lift n m x ≠ first n m ∧ lift n m x ≠ second n m := by
  cases x with
  | inr r => simp [lift,first,second]
  | inl i =>
    have hi:=i.isLt
    simp only [lift,first,second]
    split_ifs <;> simp only [Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
      Sum.inr_ne_inl,Fin.ext_iff,Fin.val_last,ne_eq,not_false_eq_true,and_true,true_and] <;> omega
lemma lift_injective : Function.Injective (lift (R:=R) n m) := by
  intro x y h
  cases x with
  | inr r =>
    cases y with
    | inr s => exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))
    | inl i => simp only [lift] at h; split_ifs at h; cases h
  | inl i =>
    cases y with
    | inr s => simp only [lift] at h; split_ifs at h; cases h
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [lift] at h
      split_ifs at h <;> simp only [Sum.inl.injEq,Sum.inr.injEq,Fin.ext_iff] at h
      all_goals omega
lemma lift_surjective (x : Old (R:=R) n m) (hp : x ≠ first n m) (hq : x ≠ second n m) :
    ∃ y, lift n m y = x := by
  rcases x with i | j | r
  · have hi : i.val < n := by
      have hh:=i.isLt
      have hn : i.val ≠ n := fun he => hp (congrArg Sum.inl (Fin.ext he))
      omega
    exact ⟨.inl ⟨i.val,by omega⟩,by simp only [lift,hi,dite_eq_left]⟩
  · have hj : j.val < m := by
      have hh:=j.isLt
      have hn : j.val ≠ m := fun he => hq (congrArg (Sum.inr ∘ Sum.inl) (Fin.ext he))
      omega
    refine ⟨.inl ⟨n+j.val,by omega⟩,?_⟩
    simp only [lift,show ¬ n+j.val<n by omega,Nat.add_sub_cancel_left]
    rfl
  · exact ⟨.inr r,rfl⟩

def residual : (Fin (n+m) ⊕ R) ≃ BandEuler.Residual (first (R:=R) n m) (second n m) (different n m) :=
  Equiv.ofBijective
    (fun x => ⟨⟨lift n m x,(lift_ne n m x).1⟩,by
      intro h; exact (lift_ne n m x).2 (congrArg Subtype.val h)⟩)
    ⟨fun _ _ h => lift_injective n m (congrArg (BandEuler.val _ _ _) h),by
      intro x
      obtain ⟨y,hy⟩:=lift_surjective n m (BandEuler.val _ _ _ x)
        (BandEuler.val_ne_p _ _ _ x) (BandEuler.val_ne_q _ _ _ x)
      exact ⟨y, BandEuler.val_injective _ _ _ hy⟩⟩
lemma residual_val (x : Fin (n+m) ⊕ R) :
    BandEuler.val _ _ _ (residual n m x) = lift n m x := rfl
variable (ρ : Equiv.Perm R)
def oldRotation : Equiv.Perm (Old (R:=R) n m) :=
  Equiv.sumCongr (finRotate (n+1)) (Equiv.sumCongr (finRotate (m+1)) ρ)
lemma residual_rotation (x : Fin (n+m) ⊕ R) :
    BandEuler.rotation (oldRotation n m ρ) (first n m) (second n m) (different n m)
      (residual n m x) = residual n m (Equiv.sumCongr (finRotate (n+m)) ρ x) := by
  apply BandEuler.val_injective
  rw [Smoothing.rotation_value,residual_val,residual_val]
  rcases x with i | r
  · have hi:=i.isLt
    by_cases hn : i.val < n
    all_goals
      simp only [oldRotation,BandEuler.switched,Equiv.Perm.mul_apply,
        Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,lift,hn,dite_true,dite_false,
        first,second,Equiv.swap_apply_def,finRotate_last,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.ext_iff,
        Fin.val_last,Fin.val_zero,ContiguousSplit.rotate_val,ite_false]
      split_ifs <;> simp_all only [Sum.inl.injEq,Sum.inr.injEq,Fin.ext_iff,Fin.val_last,Fin.val_zero,ContiguousSplit.rotate_val,
        ite_true,ite_false]
      all_goals first | contradiction | omega
  · simp [oldRotation,BandEuler.switched,Equiv.Perm.mul_apply,lift,first,second,
      Equiv.swap_apply_def]
end Numeric
end MergeChart
end
end Blueprint.DiagramProof

