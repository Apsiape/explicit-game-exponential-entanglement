import Blueprint.A.LocalBasic
import Mathlib.GroupTheory.Perm.Support

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

/-- A permutation supported on a finite set uses at most |S|-1 swaps,
and every endpoint stays in that set. No presentation hypothesis is used. -/
theorem finite_swap_factorization {α : Type} [DecidableEq α]
    (S : Finset α) (g : Equiv.Perm α) (hg : ∀ x, g x≠x → x∈S) :
    ∃ xs : List (α × α), xs.length≤S.card-1 ∧
      (∀ a∈xs, a.1∈S ∧ a.2∈S) ∧
      (xs.map (fun a => Equiv.swap a.1 a.2)).prod=g := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S g with
  | h n ih =>
    by_cases he : g=1
    · exact ⟨[],by simp,by simp,by simp [he]⟩
    obtain ⟨x,hx⟩ : ∃ x, g x≠x := by
      by_contra h
      apply he
      apply Equiv.ext
      intro x
      simp only [not_exists,not_not] at h
      exact h x
    have hxS := hg x hx
    have hyS : g x∈S := hg (g x) (fun h => hx (g.injective h))
    have htwo : 2≤S.card := by
      have hc : ({x,g x}:Finset α)⊆S := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl|hz
        · exact hxS
        · exact Finset.mem_singleton.mp hz ▸ hyS
      have hh := Finset.card_le_card hc
      simpa only [Finset.card_pair hx.symm] using hh
    let T := S.erase x
    let f := Equiv.swap x (g x)*g
    have hT : T.card=S.card-1 := Finset.card_erase_of_mem hxS
    have hf : ∀ y, f y≠y → y∈T := by
      intro y hy
      have hh := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
      exact Finset.mem_erase.mpr ⟨hh.2,hg y hh.1⟩
    obtain ⟨xs,hl,hm,hp⟩ := ih T.card (by omega) T f hf rfl
    refine ⟨(x,g x)::xs,?_,?_,?_⟩
    · simp only [List.length_cons]
      omega
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact ⟨hxS,hyS⟩
      · exact ⟨Finset.mem_of_mem_erase (hm a ha).1,Finset.mem_of_mem_erase (hm a ha).2⟩
    · simp only [List.map_cons,List.prod_cons,hp,f,←mul_assoc,Equiv.swap_mul_self,one_mul]

/-- A finite supporting set for a product is the union of supporting sets. -/
theorem finite_support_mul {α : Type} [DecidableEq α]
    (g h : Equiv.Perm α) (S T : Finset α)
    (hg : ∀ x, g x≠x → x∈S) (hh : ∀ x, h x≠x → x∈T) :
    ∀ x, (g*h) x≠x → x∈S∪T := by
  intro x hx
  by_cases ht : x∈T
  · exact Finset.mem_union_right _ ht
  · have he : h x=x := by by_contra hn; exact ht (hh x hn)
    exact Finset.mem_union_left _ (hg x (by simpa only [Equiv.Perm.mul_apply,he] using hx))

theorem finite_support_inv {α : Type} [DecidableEq α]
    (g : Equiv.Perm α) (S : Finset α) (hg : ∀ x, g x≠x → x∈S) :
    ∀ x, g⁻¹ x≠x → x∈S := by
  intro x hx
  apply hg x
  intro he
  apply hx
  exact g.injective ((g.apply_symm_apply x).trans he.symm)

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.finite_swap_factorization
#print axioms Blueprint.PairProof.finite_support_mul
#print axioms Blueprint.PairProof.finite_support_inv
