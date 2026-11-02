import Companion.Kernel
namespace Companion

def substituteWords (images : Nat → Word) (w : Word) : Word :=
  w.flatMap fun a => if a.2 then images a.1 else FreeGroup.invRev (images a.1)

theorem mk_substituteWords (images : Nat → Word) (w : Word) :
    FreeGroup.mk (substituteWords images w) =
      FreeGroup.lift (fun j => FreeGroup.mk (images j)) (FreeGroup.mk w) := by
  induction w with
  | nil => simp [substituteWords,FreeGroup.lift_mk,← FreeGroup.one_eq_mk]
  | cons a w ih =>
    simp only [substituteWords,List.flatMap_cons,← FreeGroup.mul_mk,
      FreeGroup.lift_mk,List.map_cons,List.prod_cons] at *
    rw [ih]
    cases a.2 <;> simp [FreeGroup.inv_mk]

def presentationWords (p : Presentation) : List Word :=
  (List.range p.n0).map (fun j => [pos j,pos j]) ++
  p.linear.map (fun vs => vs.map pos) ++
  p.c0.map (fun (a,b,c) => [pos a,pos b,pos a,neg c]) ++
  p.c1.map (fun (b,c) => [pos p.n0,pos b,neg p.n0,neg c])

theorem presentationRelator_mem {p : Presentation} {k : RelKey} {r : Word}
    (h : presentationRelator p k=some r) : r ∈ presentationWords p := by
  cases k with
  | square j =>
    by_cases hj : j<p.n0
    · have he : r=[pos j,pos j] := by simpa [presentationRelator,hj] using h.symm
      subst r
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)))
    · simp [presentationRelator,hj] at h
  | equation j =>
    cases he : p.linear[j]? with
    | none => simp [presentationRelator,he] at h
    | some vs =>
      have hr : r=vs.map pos := by simpa [presentationRelator,he] using h.symm
      subst r
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨vs,List.mem_of_getElem? he,rfl⟩)))
  | conjugacy j =>
    cases he : p.c0[j]? with
    | none => simp [presentationRelator,he] at h
    | some t =>
      rcases t with ⟨a,b,c⟩
      have hr : r=[pos a,pos b,pos a,neg c] := by simpa [presentationRelator,he] using h.symm
      subst r
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨(a,b,c),List.mem_of_getElem? he,rfl⟩))
  | pConjugacy j =>
    cases he : p.c1[j]? with
    | none => simp [presentationRelator,he] at h
    | some t =>
      rcases t with ⟨b,c⟩
      have hr : r=[pos p.n0,pos b,neg p.n0,neg c] := by simpa [presentationRelator,he] using h.symm
      subst r
      exact List.mem_append_right _ (List.mem_map.mpr ⟨(b,c),List.mem_of_getElem? he,rfl⟩)
  | commute _ _ _ | central _ | centralSquare => simp [presentationRelator] at h

end Companion
