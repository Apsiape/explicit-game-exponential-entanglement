import Blueprint.A.Diagram.MergeChart
namespace Blueprint.DiagramProof
open scoped Classical
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
noncomputable section
namespace MergeChart

def source (u v : Word) (e : Nat × Bool) (ws : List Word) :
    WordBlocks.Occ ((u ++ [e]) :: (v ++ [inverse e]) :: ws) ≃ Old (R:=WordBlocks.Occ ws) u.length v.length :=
  Equiv.sumCongr (finCongr (by simp))
    (Equiv.sumCongr (finCongr (by simp)) (Equiv.refl _))
lemma source_rotation (u v : Word) (e : Nat × Bool) (ws : List Word) :
    (source u v e ws).permCongr
      (BlockBoundary.rotation (WordBlocks.lengths ((u ++ [e]) :: (v ++ [inverse e]) :: ws))) =
    oldRotation u.length v.length (BlockBoundary.rotation (WordBlocks.lengths ws)) := by
  apply Equiv.ext
  intro x
  rcases x with i | j | r
  · apply congrArg Sum.inl
    exact Equiv.congr_fun (WordBlocks.finRotate_congr (by simp)) i
  · apply congrArg (Sum.inr ∘ Sum.inl)
    exact Equiv.congr_fun (WordBlocks.finRotate_congr (by simp)) j
  · rfl

def target (u v : Word) (ws : List Word) :
    WordBlocks.Occ ((u ++ v) :: ws) ≃
      BandEuler.Residual (first (R:=WordBlocks.Occ ws) u.length v.length)
        (second u.length v.length) (different u.length v.length) :=
  (Equiv.sumCongr (finCongr (by simp)) (Equiv.refl _)).trans (residual u.length v.length)
lemma target_rotation (u v : Word) (ws : List Word) (x : WordBlocks.Occ ((u ++ v) :: ws)) :
    BandEuler.rotation (oldRotation u.length v.length (BlockBoundary.rotation (WordBlocks.lengths ws)))
      (first u.length v.length) (second u.length v.length) (different u.length v.length)
      (target u v ws x) = target u v ws (BlockBoundary.rotation (WordBlocks.lengths ((u ++ v) :: ws)) x) := by
  change BandEuler.rotation _ _ _ _
    (residual u.length v.length (Equiv.sumCongr (finCongr (by simp)) (Equiv.refl _) x)) =
    residual u.length v.length (Equiv.sumCongr (finCongr (by simp)) (Equiv.refl _)
      (BlockBoundary.rotation (WordBlocks.lengths ((u ++ v) :: ws)) x))
  rw [residual_rotation]
  apply congrArg (residual u.length v.length)
  cases x with
  | inl i =>
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [ContiguousSplit.rotate_val,finCongr_apply,Fin.val_cast,List.length_append]
  | inr r => rfl

lemma target_letter (u v : Word) (e : Nat × Bool) (ws : List Word)
    (x : WordBlocks.Occ ((u ++ v) :: ws)) :
    WordBlocks.letter ((u ++ [e]) :: (v ++ [inverse e]) :: ws)
      ((source u v e ws).symm (BandEuler.val _ _ _ (target u v ws x))) =
      WordBlocks.letter ((u ++ v) :: ws) x := by
  cases x with
  | inr r => rfl
  | inl i =>
    change WordBlocks.letter _ ((source u v e ws).symm
      (lift u.length v.length (.inl (finCongr (by simp) i)))) = (u ++ v).get i
    by_cases hi : i.val < u.length
    · simp only [lift,finCongr_apply,Fin.val_cast,hi,dite_true]
      change (u ++ [e])[i.val]'(by simp; omega) = (u ++ v)[i.val]
      rw [List.getElem_append_left hi,List.getElem_append_left hi]
    · simp only [lift,finCongr_apply,Fin.val_cast,hi,dite_false]
      change (v ++ [inverse e])[i.val-u.length]'(by have hh:=i.isLt; simp only [List.length_append,List.length_singleton] at *; omega) = (u ++ v)[i.val]
      rw [List.getElem_append_right (Nat.le_of_not_gt hi),List.getElem_append_left (by
        have hh:=i.isLt; simp only [List.length_append] at hh; omega)]

/-- Merge two literal words whose selected inverse letters are at their ends. -/
theorem merge_ends (u v : Word) (e : Nat × Bool) (ws : List Word)
    (d : WordBlocks.Matching inverse ((u ++ [e]) :: (v ++ [inverse e]) :: ws))
    (hp : d.partner (.inl ⟨u.length,by simp⟩) = .inr (.inl ⟨v.length,by simp⟩)) :
    Nonempty (WordBlocks.Matching inverse ((u ++ v) :: ws)) := by
  let : DecidableEq (Old (R:=WordBlocks.Occ ws) u.length v.length) := fun _ _ => Classical.propDecidable _
  let s := source u v e ws
  let t := target u v ws
  let α := s.permCongr d.partner
  let σ := oldRotation u.length v.length (BlockBoundary.rotation (WordBlocks.lengths ws))
  let p := first (R:=WordBlocks.Occ ws) u.length v.length
  let q := second (R:=WordBlocks.Occ ws) u.length v.length
  have hi : Function.Involutive α := PermutationTransport.involutive s _ d.involutive
  have hf : ∀x, α x ≠ x := PermutationTransport.fixed_free s _ d.fixed_free
  have hpair : α p = q := by
    change s (d.partner (s.symm p)) = q
    change s (d.partner (.inl ⟨u.length,by simp⟩)) = q
    rw [hp]
    rfl
  have hz : MapEuler.GenusZero σ α := by
    have h:=MapConjugation.genusZero s _ _ d.genusZero
    rw [source_rotation] at h
    exact h
  let β := BandEuler.partner α hi p q (different u.length v.length) hpair
  have bi : Function.Involutive β := BandEuler.partner_involutive α hi p q _ hpair
  have bf : ∀x, β x ≠ x := BandEuler.partner_distinct α hi p q _ hpair hf
  refine ⟨⟨t.symm.permCongr β,
    PermutationTransport.involutive t.symm _ bi,
    PermutationTransport.fixed_free t.symm _ bf,?_,?_⟩⟩
  · intro x
    have hc := d.compatible (s.symm (BandEuler.val p q _ (t x)))
    have hv := BandEuler.partner_val α hi p q (different u.length v.length) hpair (t x)
    change BandEuler.val p q _ (β (t x)) = α (BandEuler.val p q _ (t x)) at hv
    rw [← target_letter u v e ws x]
    change WordBlocks.letter _ (t.symm (β (t x))) = _
    rw [← target_letter u v e ws (t.symm (β (t x)))]
    change WordBlocks.letter _ (s.symm (BandEuler.val p q _ (t (t.symm (β (t x)))))) =
      inverse (WordBlocks.letter _ (s.symm (BandEuler.val p q _ (t x))))
    rw [Equiv.apply_symm_apply,hv]
    simpa only [α,Equiv.permCongr_apply,Equiv.symm_apply_apply] using hc
  · have h:=MapConjugation.genusZero t.symm _ _ (BandEuler.genusZero_all σ α hi p q _ hpair hz)
    convert h using 1
    apply Equiv.ext
    intro x
    change _ = t.symm (BandEuler.rotation σ p q _ (t x))
    rw [target_rotation]
    exact (t.symm_apply_apply _).symm
end MergeChart
end
end Blueprint.DiagramProof
