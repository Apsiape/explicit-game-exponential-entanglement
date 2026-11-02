import Blueprint.A.Diagram.Specification
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
/-- Stem removal is the cap splice, without imposing a length bound on stems. -/
theorem remove_conjugator (c w : Word) (ws : List Word)
    (d : WordBlocks.Matching inverse ((c ++ w ++ FreeGroup.invRev c) :: ws)) :
    Nonempty (WordBlocks.Matching inverse (w :: ws)) := by
  induction c with
  | nil => exact ⟨by simpa only [List.nil_append,FreeGroup.invRev_empty,List.append_nil] using d⟩
  | cons a c ih =>
    have he : (a::c) ++ w ++ FreeGroup.invRev (a::c) =
        a :: ((c ++ w ++ FreeGroup.invRev c) ++ [inverse a]) := by
      simp only [FreeGroup.invRev,List.reverse_cons,List.map_cons,
        List.cons_append,List.append_assoc,inverse]
    rw [he] at d
    exact ih (d.removeCaps (fun e => by cases e; simp [inverse]) a
      (c ++ w ++ FreeGroup.invRev c) ws)
/-- Strip all conjugators from a literal inverse product, retaining face count. -/
theorem strip_factors (fs : List WordFactor) (pre : List Word)
    (d : WordBlocks.Matching inverse
      (pre ++ fs.map (fun f => f.1 ++ signedWord f.2.1 (!f.2.2) ++ FreeGroup.invRev f.1))) :
    Nonempty (WordBlocks.Matching inverse
      (pre ++ fs.map (fun f => signedWord f.2.1 (!f.2.2)))) := by
  induction fs generalizing pre with
  | nil => exact ⟨d⟩
  | cons f fs ih =>
    change WordBlocks.Matching inverse
      (pre ++ (f.1 ++ signedWord f.2.1 (!f.2.2) ++ FreeGroup.invRev f.1) ::
        fs.map (fun f => f.1 ++ signedWord f.2.1 (!f.2.2) ++ FreeGroup.invRev f.1)) at d
    obtain ⟨dnew⟩ := remove_conjugator f.1 (signedWord f.2.1 (!f.2.2))
      (pre ++ fs.map (fun f => f.1 ++ signedWord f.2.1 (!f.2.2) ++ FreeGroup.invRev f.1)) d.focus
    have dback := dnew.unfocus (ws := pre)
    obtain ⟨dnext⟩ := ih (pre ++ [signedWord f.2.1 (!f.2.2)])
      (by simpa only [List.append_assoc,List.singleton_append] using dback)
    exact ⟨by simpa only [List.map_cons,List.append_assoc,List.singleton_append] using dnext⟩
/-- The given bounded-area factor list, rather than a new unbounded normal-
closure witness, supplies a finite permutation diagram at the same area. -/
theorem initial (R : Finset Word) (K k : Nat) (w : Word)
    (hR : ∀ r ∈ R, r.length ≤ K) (ha : finiteWordArea R w k) :
    ∃ n, n ≤ k ∧ Nonempty (Diagram R K w n) := by
  obtain ⟨fs,hlen,hmem,hprod⟩ := ha
  let invWord : WordFactor → Word := fun f =>
    f.1 ++ signedWord f.2.1 (!f.2.2) ++ FreeGroup.invRev f.1
  have hi (f : WordFactor) : FreeGroup.mk (invWord f) = (wordFactorValue f)⁻¹ := by
    cases hb : f.2.2 <;>
      simp [invWord,signedWord,hb,←FreeGroup.mul_mk,←FreeGroup.inv_mk,
        wordFactorValue,mul_inv_rev,mul_assoc]
  have hv : FreeGroup.mk (fs.reverse.map invWord).flatten =
      ((fs.map wordFactorValue).prod)⁻¹ := by
    suffices hh : ∀ gs : List WordFactor,
        FreeGroup.mk (gs.reverse.map invWord).flatten = ((gs.map wordFactorValue).prod)⁻¹ from hh fs
    intro gs
    induction gs with
    | nil => exact FreeGroup.one_eq_mk.symm
    | cons f gs ih =>
      simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
        List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
        ←FreeGroup.mul_mk,ih,hi,List.prod_cons,mul_inv_rev]
  obtain ⟨d⟩ := WordBlocks.of_identity (w :: fs.reverse.map invWord) (by
    simp only [List.flatten_cons,←FreeGroup.mul_mk,hv,hprod,mul_inv_cancel])
  obtain ⟨s⟩ := strip_factors fs.reverse [w] d
  let faces : List Face := fs.reverse.map (fun f => (f.2.1,!f.2.2))
  refine ⟨fs.length,hlen,⟨⟨faces,by simp [faces],?_,?_⟩⟩⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg' := List.mem_reverse.mp hg
    exact ⟨hmem g hg',hR _ (hmem g hg')⟩
  · simpa only [faces,faceWord,List.map_map,Function.comp_def,List.singleton_append] using s
end Blueprint.DiagramProof
