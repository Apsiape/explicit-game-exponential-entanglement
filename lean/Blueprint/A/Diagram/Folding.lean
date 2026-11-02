import Blueprint.A.Diagram.Merge
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
/-- Merge the actual two cyclic boundaries at a matched inverse pair. This is
the paired-band operation followed by deletion of its two selected darts.
It allows arbitrary empty prefixes, suffixes and other boundary components. -/
theorem merge_matching (a z p q : Word) (e : Nat × Bool) (pre post : List Word)
    (d : WordBlocks.Matching inverse
      ((a ++ [e] ++ z) :: (pre ++ (p ++ [inverse e] ++ q) :: post)))
    (hp : d.partner (Sum.inl (edgeAt a e z)) =
      Sum.inr (blockAt pre (p ++ [inverse e] ++ q) post (edgeAt p (inverse e) q))) :
    Nonempty (WordBlocks.Matching inverse ((a ++ q ++ p ++ z) :: (pre ++ post))) :=
  MergeChart.merge a z p q e pre post d hp
/-- Convert the removed, possibly unreduced signed relator back to the original
relator. The last-letter cut is separate so the transport bound remains K-1. -/
theorem signed_face (R : Finset Word) (K : Nat) (r : Word) (b : Bool)
    (a z p q : Word) (e : Nat × Bool) (hr : r ∈ R) (hK : r.length ≤ K)
    (hs : signedWord r b = p ++ [inverse e] ++ q) :
    Nonempty (FaceCollapse R K (a ++ [e] ++ z) (a ++ q ++ p ++ z)) := by
  have hl := signedWord_length r b
  rw [hs,List.length_append,List.length_append,List.length_singleton] at hl
  have hinv : FreeGroup.mk [inverse e] = (FreeGroup.mk [e])⁻¹ := by
    rw [FreeGroup.inv_mk]
    rfl
  have hsign : wordFactorValue ([],r,!b) = (FreeGroup.mk (signedWord r b))⁻¹ := by
    cases b <;> simp [wordFactorValue,signedWord]
  have hvalue (v : Word) : wordFactorValue (v,r,!b) =
      FreeGroup.mk v * (FreeGroup.mk (signedWord r b))⁻¹ * (FreeGroup.mk v)⁻¹ := by
    have hh := hsign
    simp only [wordFactorValue,←FreeGroup.one_eq_mk,one_mul,inv_one,mul_one] at hh
    simp only [wordFactorValue,hh]
  by_cases hq : q = []
  · subst q
    refine ⟨⟨a,z,e,[] ++ p,r,!b,[],hr,rfl,by simp only [List.append_assoc],by simp; omega,by simp; omega,?_⟩⟩
    rw [hvalue,hs]
    simp only [List.nil_append,List.append_nil,←FreeGroup.mul_mk,←FreeGroup.inv_mk,
      ←FreeGroup.one_eq_mk,one_mul,inv_one,mul_one,hinv,mul_inv_rev,inv_inv]
  · have hqp : 0 < q.length := List.length_pos_iff.mpr hq
    refine ⟨⟨a,z,e,q ++ p,r,!b,FreeGroup.invRev (p ++ [inverse e]),hr,rfl,by simp only [List.append_assoc],
      by simp only [List.length_append]; omega,
      by simp only [FreeGroup.invRev_length,List.length_append,List.length_singleton]; omega,?_⟩⟩
    rw [hvalue,hs]
    simp only [←FreeGroup.mul_mk,←FreeGroup.inv_mk,hinv]
    group
/-- Remove one original face while preserving the entire finite matching.
A new face order may be selected at the next recursive step. -/
theorem collapse {R : Finset Word} {K n : Nat} {u : Word} (c : Contact R K u n) :
    ∃ v m, m + 1 = n ∧ Nonempty (FaceCollapse R K u v) ∧
      Nonempty (Diagram R K v m) := by
  obtain ⟨s⟩ := merge_matching c.before c.after c.left c.right c.edge
    (c.pre.map faceWord) (c.post.map faceWord) c.matching c.paired
  obtain ⟨f⟩ := signed_face R K c.original c.positive c.before c.after c.left c.right
    c.edge c.original_mem c.original_length c.original_split
  refine ⟨c.before ++ c.right ++ c.left ++ c.after,c.pre.length+c.post.length,
    c.count,?_,?_⟩
  · exact ⟨Eq.mp (congrArg (fun w => FaceCollapse R K w
      (c.before ++ c.right ++ c.left ++ c.after)) c.source.symm) f⟩
  · refine ⟨⟨c.pre ++ c.post,by simp,c.valid,?_⟩⟩
    simpa only [List.map_append,List.append_assoc] using s
end Blueprint.DiagramProof
