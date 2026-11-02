import Blueprint.A.Diagram.Specification
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
private theorem rotate_cast {n m : Nat} (h : n = m) (i : Fin n) :
    finCongr h (finRotate n i) = finRotate m (finCongr h i) := by subst m; rfl
private def shiftLast (u : Word) (e : Nat × Bool) (ws : List Word) :
    WordBlocks.Occ ((u ++ [e]) :: ws) ≃ WordBlocks.Occ ((e :: u) :: ws) :=
  Equiv.sumCongr ((finCongr (by simp)).trans (finRotate _)) (Equiv.refl _)
theorem rotate_last (u : Word) (e : Nat × Bool) (ws : List Word)
    (d : WordBlocks.Matching inverse ((u ++ [e]) :: ws)) :
    Nonempty (WordBlocks.Matching inverse ((e :: u) :: ws)) := by
  refine ⟨d.rename (shiftLast u e ws) ?_ ?_⟩
  · intro i
    cases i with
    | inr i => rfl
    | inl i =>
      change (e :: u)[(finRotate (e :: u).length (finCongr (by simp) i)).val] =
        (u ++ [e])[i.val]
      by_cases hi : i.val < u.length
      · have hr : (finRotate (e :: u).length (finCongr (by simp) i)).val = i.val + 1 := by
          rw [ContiguousSplit.rotate_val]
          change (if i.val+1=u.length+1 then 0 else i.val+1) = i.val+1
          exact ite_eq_right (by omega)
        simp only [hr,List.getElem_cons_succ,List.getElem_append_left hi]
      · have he : i.val = u.length := by have hh := i.isLt; simp only [List.length_append,List.length_singleton] at hh; omega
        have hr : (finRotate (e :: u).length (finCongr (by simp) i)).val = 0 := by
          rw [ContiguousSplit.rotate_val]
          change (if i.val+1=u.length+1 then 0 else i.val+1) = 0
          exact ite_eq_left (by omega)
        simp only [hr,List.getElem_cons_zero,he]
        simp
  · intro i
    cases i with
    | inr i => rfl
    | inl i =>
      apply congrArg Sum.inl
      change finRotate _ (finCongr _ (finRotate _ i)) =
        finRotate _ (finRotate _ (finCongr _ i))
      rw [rotate_cast]
/-- A cyclic cut is moved without changing any original boundary labels. -/
theorem rotate_blocks (p q : Word) (ws : List Word)
    (d : WordBlocks.Matching inverse ((p ++ q) :: ws)) :
    Nonempty (WordBlocks.Matching inverse ((q ++ p) :: ws)) := by
  induction q using List.reverseRecOn generalizing p with
  | nil => exact ⟨by simpa only [List.nil_append,List.append_nil] using d⟩
  | append_singleton q e ih =>
    obtain ⟨s⟩ := rotate_last (p ++ q) e ws
      (by simpa only [List.append_assoc] using d)
    obtain ⟨v⟩ := ih ([e] ++ p)
      (by simpa only [List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using s)
    exact ⟨by simpa only [List.append_assoc] using v⟩
/-- Boundary folding retains the full partner structure, including when a
selected face arc disappears. Partners are spliced by the proved cap operation. -/
theorem cancel_pair (a z : Word) (e : Nat × Bool) (ws : List Word)
    (d : WordBlocks.Matching inverse ((a ++ [e,inverse e] ++ z) :: ws)) :
    Nonempty (WordBlocks.Matching inverse ((a ++ z) :: ws)) := by
  obtain ⟨s⟩ := rotate_blocks (a ++ [e]) (inverse e :: z) ws
    (by simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using d)
  have he : inverse (inverse e) = e := by cases e; simp [inverse]
  have sn : WordBlocks.Matching inverse
      ((inverse e :: ((z ++ a) ++ [inverse (inverse e)])) :: ws) := by
    simpa only [he,List.cons_append,List.append_assoc] using s
  let v := sn.removeCaps (fun x => by cases x; simp [inverse]) (inverse e) (z ++ a) ws
  exact rotate_blocks z a ws v
/-- Any finite free reduction folds only the exterior, retaining all faces. -/
theorem reduce_matching {u v : Word} (h : FreeGroup.Red u v) (ws : List Word)
    (d : WordBlocks.Matching inverse (u :: ws)) :
    Nonempty (WordBlocks.Matching inverse (v :: ws)) := by
  induction h with
  | refl => exact ⟨d⟩
  | tail h step ih =>
    obtain ⟨s⟩ := ih
    cases step with
    | @not a z x b =>
      exact cancel_pair a z (x,b) ws (by
        simpa only [inverse,List.cons_append,List.nil_append,List.append_assoc] using s)
end Blueprint.DiagramProof
