import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Companion.FiniteArea
open scoped BigOperators

abbrev Factor (α ι : Type) := FreeGroup α × ι × Bool
def factorValue {α ι : Type} (R : ι → FreeGroup α) (f : Factor α ι) : FreeGroup α :=
  f.1*(if f.2.2 then R f.2.1 else (R f.2.1)⁻¹)*f.1⁻¹

def Area {α ι : Type} (R : ι → FreeGroup α) (w : FreeGroup α) (bound : Nat) : Prop :=
  ∃ fs : List (Factor α ι), fs.length≤bound ∧ (fs.map (factorValue R)).prod=w

theorem exists_witness_of_normalClosure {α ι : Type} (R : ι → FreeGroup α) (w : FreeGroup α)
    (hw : w ∈ Subgroup.normalClosure (Set.range R)) :
    ∃ fs : List (Factor α ι), (fs.map (factorValue R)).prod=w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r,⟨i,rfl⟩,hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨q,hq⟩ := isConj_iff.mp hconj
    exact ⟨[(q,i,true)],by simpa [factorValue] using hq⟩
  | one => exact ⟨[],by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨xs,hxs⟩ := ihx
    obtain ⟨ys,hys⟩ := ihy
    exact ⟨xs++ys,by simp [List.map_append,List.prod_append,hxs,hys]⟩
  | inv x _ ih =>
    obtain ⟨xs,hxs⟩ := ih
    let flip : Factor α ι → Factor α ι := fun f => (f.1,f.2.1,!f.2.2)
    have hf (f : Factor α ι) : factorValue R (flip f)=(factorValue R f)⁻¹ := by
      rcases f with ⟨q,i,b⟩
      cases b <;> simp [factorValue,flip,mul_inv_rev,mul_assoc]
    refine ⟨(xs.map flip).reverse,?_⟩
    simp only [List.map_reverse,List.map_map,Function.comp_def,hf]
    calc
      _ = ((xs.map (factorValue R)).map (fun x => x⁻¹)).reverse.prod := by rw [List.map_map]; rfl
      _ = ((xs.map (factorValue R)).prod)⁻¹ := (List.prod_inv_reverse _).symm
      _ = _ := congrArg (fun x => x⁻¹) hxs

theorem exists_area_of_quotient {α ι : Type} (R : ι → FreeGroup α) (w : FreeGroup α)
    (hw : PresentedGroup.mk (Set.range R) w=1) : ∃ n, Area R w n := by
  obtain ⟨fs,hfs⟩ := exists_witness_of_normalClosure R w (PresentedGroup.mk_eq_one_iff.mp hw)
  exact ⟨fs.length,fs,le_rfl,hfs⟩

/-- Finitely many null words have a common finite area bound. This constructs
ordinary finite products of conjugates, rather than assuming area completeness. -/
theorem uniform_bound {α ι κ : Type} [Fintype κ] (R : ι → FreeGroup α) (W : κ → FreeGroup α)
    (hw : ∀ k, PresentedGroup.mk (Set.range R) (W k)=1) :
    ∃ A : Nat, 1≤A ∧ ∀ k, Area R (W k) A := by
  classical
  have hcert k := exists_area_of_quotient R (W k) (hw k)
  let bound : κ → Nat := fun k => Classical.choose (hcert k)
  refine ⟨1+∑ k, bound k,by omega,?_⟩
  intro k
  obtain ⟨fs,hfs,he⟩ := Classical.choose_spec (hcert k)
  refine ⟨fs,hfs.trans ?_,he⟩
  have hb : bound k≤∑ j, bound j := Finset.single_le_sum (fun j _ => Nat.zero_le (bound j)) (Finset.mem_univ k)
  exact hb.trans (by omega)

end Companion.FiniteArea
