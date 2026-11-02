import Blueprint.AWordArea

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators

theorem relator_support (g : Game) (k : RelKey) (r : Word)
    (hr : relator g k=some r) : ∀ a∈r, 1≤a.1 ∧ a.1≤g.n+1 := by
  cases k with
  | square j =>
    simp only [relator] at hr
    split at hr
    next hj =>
      cases Option.some.inj hr
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl <;> dsimp [pos] <;> omega
    next => simp at hr
  | central j =>
    simp only [relator] at hr
    split at hr
    next hj =>
      cases Option.some.inj hr
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> dsimp [pos,neg] <;> omega
    next => simp at hr
  | centralSquare =>
    simp only [relator,Option.some.injEq] at hr
    subst r
    simp [pos]
  | equation i =>
    cases hi : g.equations[i]? with
    | none => simp [relator,hi] at hr
    | some q =>
      simp only [relator,hi] at hr
      change (if q.vars.all (fun x => decide (x<g.n)) then
        some ((if q.rhs then [pos g.n] else [])++q.vars.map pos) else none)=some r at hr
      split at hr
      next h =>
        simp only [Option.some.injEq] at hr
        subst r
        intro a ha
        simp only [List.mem_append,List.mem_map] at ha
        rcases ha with ha | ⟨j,hj,rfl⟩
        · split at ha <;> simp_all [pos]
        · have hjn := of_decide_eq_true (List.all_eq_true.mp h j hj)
          dsimp [pos]
          omega
      next => simp at hr
  | commute i j k =>
    cases hi : g.equations[i]? with
    | none => simp [relator,hi] at hr
    | some q =>
      simp only [relator,hi] at hr
      change (if j<g.n ∧ k<g.n ∧ j∈q.vars ∧ k∈q.vars then
        some [pos j,pos k,neg j,neg k] else none)=some r at hr
      split at hr
      next h =>
        cases Option.some.inj hr
        intro a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> dsimp [pos,neg] <;> omega
      next => simp at hr
  | conjugacy i => simp [relator] at hr
  | pConjugacy i => simp [relator] at hr

def restrictAssignment {d : Nat} (n : Nat) (U : Nat → Mat d) (j : Nat) : Mat d :=
  if 1≤j ∧ j≤n+1 then U j else 1

theorem restricted_unitary {d : Nat} (n : Nat) (U : Nat → Mat d)
    (hU : ∀ j, IsUnitary (U j)) : ∀ j, IsUnitary (restrictAssignment n U j) := by
  intro j
  unfold restrictAssignment
  split
  · exact hU j
  · simp [IsUnitary]

theorem restricted_word {d : Nat} (n : Nat) (U : Nat → Mat d) (r : Word)
    (hr : ∀ a∈r, 1≤a.1 ∧ a.1≤n+1) :
    wordEval (restrictAssignment n U) r=wordEval U r := by
  unfold wordEval
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [restrictAssignment,ite_eq_left (hr a ha)]

theorem restricted_commutator {d : Nat} (n : Nat) (U : Nat → Mat d) (xi : Mat d)
    (e : ℝ) (he : 0≤e) (hc : ∀ j, 1≤j → j≤n+1 → hs (comm (U j) xi)≤e) :
    ∀ j, hs (comm (restrictAssignment n U j) xi)≤e := by
  intro j
  unfold restrictAssignment
  split
  next hj => exact hc j hj.1 hj.2
  next => simpa [Analytic.comm,hs] using he

theorem area_cost_bound (g : Game) (w : Word) (hw : ∃ k, HasArea g w k) :
    ∃ C : ℝ, 1≤C ∧ ∀ (d : Nat) (U : Nat → Mat d) (xi : Mat d) e,
      0≤e → (∀ j, IsUnitary (U j)) →
      (∀ k r, relator g k=some r → hs ((wordEval U r-1)*xi)≤e) →
      (∀ j, hs (comm (U j) xi)≤e) → hs ((wordEval U w-1)*xi)≤C*e := by
  obtain ⟨k,fs,_,hv,hrel⟩ := hw
  let C : ℝ := (fs.map (fun f => (1+2*f.conjugator.length:ℝ))).sum
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro d U xi e he hU hr hc
  have h := AWordArea.charged_area (relator g) U hU xi e e w fs hv hrel hr hc
  apply h.trans
  calc
    _ = C*e := by
      dsimp [C]
      suffices hh : ∀ xs : List Factor,
          (xs.map (fun f => e+2*f.conjugator.length*e)).sum=
          (xs.map (fun f => (1+2*f.conjugator.length:ℝ))).sum*e by exact hh fs
      intro xs
      induction xs with
      | nil => simp
      | cons f fs ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring
    _ ≤ max 1 C*e := mul_le_mul_of_nonneg_right (le_max_right _ _) he

theorem area_family_bound (g : Game) (ws : List Word)
    (hw : ∀ w∈ws, ∃ k, HasArea g w k) :
    ∃ C : ℝ, 1≤C ∧ ∀ (d : Nat) (U : Nat → Mat d) (xi : Mat d) e,
      0≤e → (∀ j, IsUnitary (U j)) →
      (∀ k r, relator g k=some r → hs ((wordEval U r-1)*xi)≤e) →
      (∀ j, hs (comm (U j) xi)≤e) → ∀ w∈ws, hs ((wordEval U w-1)*xi)≤C*e := by
  induction ws with
  | nil => exact ⟨1,le_rfl,by simp⟩
  | cons w ws ih =>
    obtain ⟨C,hC,hhead⟩ := area_cost_bound g w (hw w (by simp))
    obtain ⟨D,hD,htail⟩ := ih (fun v hv => hw v (by simp [hv]))
    refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
    intro d U xi e he hU hr hc v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (hhead d U xi e he hU hr hc).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) he)
    · exact (htail d U xi e he hU hr hc v hv).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) he)

end
end Blueprint.SV

#print axioms Blueprint.SV.relator_support
#print axioms Blueprint.SV.restrictAssignment
#print axioms Blueprint.SV.restricted_unitary
#print axioms Blueprint.SV.restricted_word
#print axioms Blueprint.SV.restricted_commutator
#print axioms Blueprint.SV.area_cost_bound
#print axioms Blueprint.SV.area_family_bound
