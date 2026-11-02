import Companion.Kernel

namespace Companion

/-- The checker proves an actual consequence in every group satisfying the
presentation, in addition to the explicit free-group area witness. -/
theorem HasAreaWith.consequence {G : Type*} [Group G]
    {rfn : RelKey → Option Word} {t : Word} {b : Nat}
    (ha : HasAreaWith rfn t b) (h : FreeGroup Nat →* G)
    (hr : ∀ k w, rfn k = some w → h (FreeGroup.mk w) = 1) :
    h (FreeGroup.mk t) = 1 := by
  obtain ⟨fs, _, hv, he⟩ := ha
  have factor_one (f : Factor) (hf : f ∈ fs) : h (FreeGroup.mk (factorWordWith rfn f)) = 1 := by
    cases hh : rfn f.key with
    | none => have := hv f hf; simp [hh] at this
    | some r =>
      have hh1 := hr f.key r hh
      cases hb : f.positive <;>
        simp [factorWordWith, hh, hb, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, hh1]
  have expansion_one : ∀ xs : List Factor,
      (∀ f ∈ xs, h (FreeGroup.mk (factorWordWith rfn f)) = 1) →
      h (FreeGroup.mk (expandWith rfn xs)) = 1 := by
    intro xs
    induction xs with
    | nil => intro _; simp [expandWith, ← FreeGroup.one_eq_mk]
    | cons f xs ih =>
      intro hx
      have hf := hx f (List.mem_cons_self ..)
      have ht := ih (fun x hh => hx x (List.mem_cons_of_mem f hh))
      simpa only [expandWith, List.map_cons, List.flatten_cons, ← FreeGroup.mul_mk,
        map_mul, hf, one_mul] using ht
  rw [← he]
  exact expansion_one fs factor_one

end Companion
