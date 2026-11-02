import Blueprint.A.Diagram.MergeWords
namespace Blueprint.DiagramProof
open scoped Classical
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
noncomputable section
namespace MergeChart
lemma focus_blockAt (pre : List Word) (w : Word) (post : List Word) (i : Fin w.length) :
    WordBlocks.focus pre w post (blockAt pre w post i) = Sum.inl i := by
  induction pre with
  | nil => rfl
  | cons v pre ih =>
    change WordBlocks.exchange (Sum.inr (WordBlocks.focus pre w post (blockAt pre w post i))) = _
    rw [ih]
    rfl

def markedCut (a z : Word) (e : Nat × Bool) :
    Fin (a ++ [e] ++ z).length ≃ Fin ((z ++ a) ++ [e]).length :=
  (cut (a ++ [e]) z).trans (finCongr (by simp only [List.append_assoc]))
lemma markedCut_letter (a z : Word) (e : Nat × Bool) (i : Fin (a ++ [e] ++ z).length) :
    ((z ++ a) ++ [e]).get (markedCut a z e i) = (a ++ [e] ++ z).get i := by
  change ((z ++ a) ++ [e])[(cut (a ++ [e]) z i).val] = _
  simpa only [List.append_assoc,List.get_eq_getElem] using cut_letter (a ++ [e]) z i
lemma markedCut_rotation (a z : Word) (e : Nat × Bool) (i : Fin (a ++ [e] ++ z).length) :
    markedCut a z e (finRotate _ i) = finRotate _ (markedCut a z e i) := by
  apply Fin.ext
  change (cut (a ++ [e]) z (finRotate _ i)).val = _
  rw [cut_rotation]
  simp only [ContiguousSplit.rotate_val,markedCut,Equiv.trans_apply,finCongr_apply,
    Fin.val_cast,List.length_append,Nat.add_assoc]
lemma markedCut_edge (a z : Word) (e : Nat × Bool) :
    markedCut a z e (edgeAt a e z) = ⟨(z ++ a).length,by simp⟩ := by
  apply Fin.ext
  change (cut (a ++ [e]) z (edgeAt a e z)).val = _
  rw [cut_val,ite_eq_left (by simp only [edgeAt,List.length_append,List.length_singleton]; omega)]
  simp only [edgeAt,List.length_append]

def normalize (a z p q : Word) (e : Nat × Bool) (ws : List Word) :
    WordBlocks.Occ ((a ++ [e] ++ z) :: (p ++ [inverse e] ++ q) :: ws) ≃
      WordBlocks.Occ (((z ++ a) ++ [e]) :: ((q ++ p) ++ [inverse e]) :: ws) :=
  Equiv.sumCongr (markedCut a z e)
    (Equiv.sumCongr (markedCut p q (inverse e)) (Equiv.refl _))
lemma normalize_letter (a z p q : Word) (e : Nat × Bool) (ws : List Word)
    (x : WordBlocks.Occ ((a ++ [e] ++ z) :: (p ++ [inverse e] ++ q) :: ws)) :
    WordBlocks.letter _ (normalize a z p q e ws x) = WordBlocks.letter _ x := by
  rcases x with i | j | r
  · exact markedCut_letter a z e i
  · exact markedCut_letter p q (inverse e) j
  · rfl
lemma normalize_rotation (a z p q : Word) (e : Nat × Bool) (ws : List Word)
    (x : WordBlocks.Occ ((a ++ [e] ++ z) :: (p ++ [inverse e] ++ q) :: ws)) :
    normalize a z p q e ws (BlockBoundary.rotation (WordBlocks.lengths _) x) =
      BlockBoundary.rotation (WordBlocks.lengths _) (normalize a z p q e ws x) := by
  rcases x with i | j | r
  · exact congrArg Sum.inl (markedCut_rotation a z e i)
  · exact congrArg (Sum.inr ∘ Sum.inl) (markedCut_rotation p q (inverse e) j)
  · rfl

theorem merge (a z p q : Word) (e : Nat × Bool) (pre post : List Word)
    (d : WordBlocks.Matching inverse
      ((a ++ [e] ++ z) :: (pre ++ (p ++ [inverse e] ++ q) :: post)))
    (hp : d.partner (Sum.inl (edgeAt a e z)) =
      Sum.inr (blockAt pre (p ++ [inverse e] ++ q) post (edgeAt p (inverse e) q))) :
    Nonempty (WordBlocks.Matching inverse ((a ++ q ++ p ++ z) :: (pre ++ post))) := by
  let f : WordBlocks.Occ ((a ++ [e] ++ z) :: (pre ++ (p ++ [inverse e] ++ q) :: post)) ≃
      WordBlocks.Occ ((a ++ [e] ++ z) :: (p ++ [inverse e] ++ q) :: (pre ++ post)) := Equiv.sumCongr (Equiv.refl (Fin (a ++ [e] ++ z).length))
    (WordBlocks.focus pre (p ++ [inverse e] ++ q) post)
  let d₀ : WordBlocks.Matching inverse ((a ++ [e] ++ z) :: (p ++ [inverse e] ++ q) :: (pre ++ post)) := d.rename f
    (fun x => by cases x with | inl i => rfl | inr j => exact WordBlocks.focus_letter pre _ post j)
    (fun x => by cases x with | inl i => rfl | inr j => exact congrArg Sum.inr (WordBlocks.focus_rotation pre _ post j))
  have hp₀ : d₀.partner (.inl (edgeAt a e z)) = .inr (.inl (edgeAt p (inverse e) q)) := by
    change f (d.partner (.inl (edgeAt a e z))) = _
    rw [hp]
    exact congrArg Sum.inr (focus_blockAt pre _ post _)
  let g := normalize a z p q e (pre ++ post)
  let d₁ := d₀.rename g (normalize_letter a z p q e _) (normalize_rotation a z p q e _)
  have hpair : d₁.partner (.inl ⟨(z ++ a).length,by simp⟩) =
      .inr (.inl ⟨(q ++ p).length,by simp⟩) := by
    have he₁ : g (.inl (edgeAt a e z)) = .inl ⟨(z ++ a).length,by simp⟩ :=
      congrArg Sum.inl (markedCut_edge a z e)
    have he₂ : g (.inr (.inl (edgeAt p (inverse e) q))) =
        .inr (.inl ⟨(q ++ p).length,by simp⟩) :=
      congrArg (Sum.inr ∘ Sum.inl) (markedCut_edge p q (inverse e))
    rw [←he₁,←he₂]
    change g (d₀.partner (g.symm (g (.inl (edgeAt a e z))))) = _
    exact (congrArg (fun y => g (d₀.partner y)) (g.symm_apply_apply (.inl (edgeAt a e z)))).trans (congrArg g hp₀)
  obtain ⟨s⟩ := merge_ends (z ++ a) (q ++ p) e (pre ++ post) d₁ hpair
  obtain ⟨s⟩ := rotate_blocks z (a ++ q ++ p) (pre ++ post)
    (by simpa only [List.append_assoc] using s)
  exact ⟨by simpa only [List.append_assoc] using s⟩
end MergeChart
end
end Blueprint.DiagramProof

