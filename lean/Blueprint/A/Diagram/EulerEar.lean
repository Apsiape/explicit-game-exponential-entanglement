import Blueprint.A.Diagram.Specification
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
open OAI.TorsionFreeZeroDivisors.PermutationCycles
set_option maxHeartbeats 800000
/-- Euler counting forces a monogon in a nonempty one-vertex sphere map.
This supplies the inverse-letter ear in the terminal tree case. -/
theorem euler_ear {D : Type} [Fintype D] [Nonempty D]
    (σ α : Equiv.Perm D) (hf : ∀ x, α x ≠ x)
    (ht : ∀ x y, σ.SameCycle x y) (hz : MapEuler.GenusZero σ α) :
    ∃ x, (α * σ) x = x := by
  classical
  have hv : Nat.card (Cycle σ) = 1 := by
    let : Subsingleton (Cycle σ) := ⟨by
      intro x y
      obtain ⟨x,rfl⟩ := cycle_surjective σ x
      obtain ⟨y,rfl⟩ := cycle_surjective σ y
      exact (cycle_eq σ).mpr (ht x y)⟩
    let : Nonempty (Cycle σ) := ⟨cycle σ (Classical.choice (inferInstance : Nonempty D))⟩
    exact Nat.card_unique
  have hc : Nat.card (MapEuler.Component σ α) = 1 := by
    let : Subsingleton (MapEuler.Component σ α) := ⟨by
      intro x y
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
      obtain ⟨y,rfl⟩ := Quotient.mk_surjective y
      exact MapEuler.component_sameCycle σ α (ht x y)⟩
    let : Nonempty (MapEuler.Component σ α) :=
      ⟨MapEuler.component σ α (Classical.choice (inferInstance : Nonempty D))⟩
    exact Nat.card_unique
  have hs : α.support.card = Fintype.card D := by
    simp [Equiv.Perm.support,hf]
  unfold MapEuler.GenusZero at hz
  rw [hv,hc,hs] at hz
  by_contra hn
  have hn : ∀ x, (α * σ) x ≠ x := not_exists.mp hn
  have hl : ∀ c : Cycle (α * σ), 2 ≤ (members (α * σ) c).card := by
    intro c
    have hp := Finset.card_pos.mpr (members_nonempty (α * σ) c)
    by_contra h
    have he : (members (α * σ) c).card = 1 := by omega
    obtain ⟨x,rfl⟩ := cycle_surjective (α * σ) c
    exact hn x (card_one_fixed (α * σ) he)
  have hh := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycle (α * σ)))) => hl c)
  rw [sum_card] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,←Nat.card_eq_fintype_card] at hh
  simp only [←Nat.card_eq_fintype_card] at hz
  omega
end Blueprint.DiagramProof
