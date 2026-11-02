import Blueprint.A.Diagram.Terminal
import Blueprint.A.Diagram.Occurrences
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
/-- A genus-zero matching whose partners never leave the exterior boundary
forces its word to be freely trivial. Closed interior components need not be
removed; they are irrelevant to the based exterior word. -/
theorem isolated_outer (u : Word) (ws : List Word)
    (d : WordBlocks.Matching inverse (u :: ws))
    (hi : ∀ i : Fin u.length, ∃ j : Fin u.length,
      d.partner (Sum.inl i) = Sum.inl j) : FreeGroup.mk u = 1 := by
  obtain ⟨c⟩ := restrict_outer u ws d hi
  obtain ⟨s⟩ := c.to_matching
  exact single_trivial u s
/-- Genuine outer-face existence, in the dual word-boundary representation.
It follows by splitting an actual exterior/interior matched occurrence; no
supplied shelling order or first original relator is privileged. -/
theorem outer {R : Finset Word} {K n : Nat} {u : Word} (d : Diagram R K u n) :
    FreeGroup.mk u = 1 ∨ Nonempty (Contact R K u n) := by
  classical
  obtain ⟨faces,hcount,hvalid,dm⟩ := d
  by_cases ht : ∀ i : Fin u.length, ∃ j : Fin u.length,
      dm.partner (Sum.inl i) = Sum.inl j
  · exact Or.inl (isolated_outer u (faces.map faceWord) dm ht)
  · apply Or.inr
    obtain ⟨i,hi⟩ := not_forall.mp ht
    cases hp : dm.partner (Sum.inl i) with
    | inl j => exact (hi ⟨j,hp⟩).elim
    | inr j =>
      obtain ⟨a,e,z,hu,hia,_⟩ := split_word u i
      subst u
      have hii : i = edgeAt a e z := Fin.ext hia
      subst i
      obtain ⟨f,others,ji,equiv,hperm,hl,hr,hj⟩ := focus_occurrence faces j
      let ep := Equiv.sumCongr (Equiv.refl (Fin (a ++ [e] ++ z).length)) equiv
      let dn : WordBlocks.Matching inverse
          ((a ++ [e] ++ z) :: faceWord f :: others.map faceWord) :=
        dm.rename ep (by
          intro x
          cases x with
          | inl x => rfl
          | inr x => exact hl x) (by
          intro x
          cases x with
          | inl x => rfl
          | inr x => exact congrArg Sum.inr (hr x))
      have hpn : dn.partner (Sum.inl (edgeAt a e z)) = Sum.inr (Sum.inl ji) := by
        change (ep.permCongr dm.partner) (Sum.inl (edgeAt a e z)) = _
        change ep (dm.partner (ep.symm (Sum.inl (edgeAt a e z)))) = _
        have he : ep.symm (Sum.inl (edgeAt a e z)) = Sum.inl (edgeAt a e z) := rfl
        rw [he,hp]
        change Sum.inr (equiv j) = _
        rw [hj]
        rfl
      clear_value dn
      clear hj hr hl ep equiv hp hi ht dm j
      generalize hw : faceWord f = w at ji dn hpn
      obtain ⟨p,ie,q,hwcut,hip,_⟩ := split_word w ji
      cases hwcut
      have hii : ji = edgeAt p ie q := Fin.ext hip
      subst ji
      have hlab := dn.compatible (Sum.inl (edgeAt a e z))
      rw [hpn] at hlab
      change (p ++ [ie] ++ q).get (edgeAt p ie q) =
        inverse ((a ++ [e] ++ z).get (edgeAt a e z)) at hlab
      have houter : (a ++ [e] ++ z).get (edgeAt a e z) = e := by
        simp [edgeAt,List.get_eq_getElem]
      have hinner : (p ++ [ie] ++ q).get (edgeAt p ie q) = ie := by
        simp [edgeAt,List.get_eq_getElem]
      rw [houter,hinner] at hlab
      subst ie
      have hf : f ∈ faces := hperm.mem_iff.mpr List.mem_cons_self
      obtain ⟨hmem,hK⟩ := hvalid f hf
      refine ⟨⟨[],others,f.1,f.2,a,z,p,q,e,rfl,hmem,hK,hw,?_,?_,dn,hpn⟩⟩
      · have hc := hperm.length_eq
        simp only [List.length_cons] at hc
        simpa only [List.length_nil,Nat.zero_add] using hc.symm.trans hcount
      · intro g hg
        apply hvalid g
        apply hperm.mem_iff.mpr
        exact List.mem_cons_of_mem _ (by simpa only [List.nil_append] using hg)
/-- The terminal zero-face case follows from the matching, without a supplied
free-group identity or a hidden simply-connectedness assumption. -/
theorem terminal {R : Finset Word} {K : Nat} {u : Word} (d : Diagram R K u 0) :
    FreeGroup.mk u = 1 := by
  have hf : d.faces = [] := List.length_eq_zero_iff.mp d.count
  have s : WordBlocks.Matching inverse [u] := by simpa only [hf,List.map_nil] using d.matching
  apply isolated_outer u [] s
  intro i
  cases hj : s.partner (Sum.inl i) with
  | inl j => exact ⟨j,rfl⟩
  | inr j => exact Empty.elim j
end Blueprint.DiagramProof
