import Blueprint.A.Diagram.Specification
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
theorem split_word (u : Word) (i : Fin u.length) :
    ∃ a e z, u = a ++ [e] ++ z ∧ i.val = a.length ∧ u.get i = e := by
  refine ⟨u.take i.val,u.get i,u.drop (i.val+1),?_,?_,rfl⟩
  · simpa only [List.take_succ_eq_append_getElem i.isLt,List.get_eq_getElem] using
      (List.take_append_drop (i.val+1) u).symm
  · simp only [List.length_take,Nat.min_eq_left i.isLt.le]
theorem letter_blockAt (pre : List Word) (w : Word) (post : List Word) (i : Fin w.length) :
    WordBlocks.letter (pre ++ w :: post) (blockAt pre w post i) = w.get i := by
  induction pre with
  | nil => simp only [List.nil_append,blockAt,WordBlocks.letter,Sum.elim_inl]
  | cons v pre ih =>
    simpa only [List.cons_append,blockAt,WordBlocks.letter,Sum.elim_inr] using ih
/-- Select an actual inner boundary occurrence and move its whole original
face to the first inner slot. All other faces are retained by a list permutation. -/
theorem focus_occurrence (fs : List Face) (j : WordBlocks.Occ (fs.map faceWord)) :
    ∃ (f : Face) (others : List Face) (i : Fin (faceWord f).length)
      (e : WordBlocks.Occ (fs.map faceWord) ≃
        WordBlocks.Occ (faceWord f :: others.map faceWord)),
      fs.Perm (f :: others) ∧
      (∀ x, WordBlocks.letter (faceWord f :: others.map faceWord) (e x) =
        WordBlocks.letter (fs.map faceWord) x) ∧
      (∀ x, e (BlockBoundary.rotation (WordBlocks.lengths (fs.map faceWord)) x) =
        BlockBoundary.rotation (WordBlocks.lengths (faceWord f :: others.map faceWord)) (e x)) ∧
      e j = Sum.inl i := by
  induction fs with
  | nil => exact Empty.elim j
  | cons g fs ih =>
    cases j with
    | inl i => exact ⟨g,fs,i,Equiv.refl _,List.Perm.refl _,fun _ => rfl,fun _ => rfl,rfl⟩
    | inr j =>
      obtain ⟨f,others,i,e,hperm,hl,hr,hj⟩ := ih j
      let ep := (Equiv.sumCongr (Equiv.refl (Fin (faceWord g).length)) e).trans WordBlocks.exchange
      refine ⟨f,g :: others,i,ep,
        (List.Perm.cons g hperm).trans (List.Perm.swap f g others),?_,?_,?_⟩
      · intro x
        cases x with
        | inl x => rfl
        | inr x =>
          change Sum.elim (faceWord f).get
            (Sum.elim (faceWord g).get (WordBlocks.letter (others.map faceWord)))
            (WordBlocks.exchange (Sum.inr (e x))) = WordBlocks.letter (fs.map faceWord) x
          rw [WordBlocks.exchange_letter]
          exact hl x
      · intro x
        cases x with
        | inl x => rfl
        | inr x =>
          change WordBlocks.exchange (Sum.inr
            (e (BlockBoundary.rotation (WordBlocks.lengths (fs.map faceWord)) x))) = _
          rw [hr]
          exact WordBlocks.exchange_rotation (finRotate (faceWord g).length)
            (finRotate (faceWord f).length)
            (BlockBoundary.rotation (WordBlocks.lengths (others.map faceWord))) (Sum.inr (e x))
      · change WordBlocks.exchange (Sum.inr (e j)) = _
        rw [hj]
        rfl
end Blueprint.DiagramProof
