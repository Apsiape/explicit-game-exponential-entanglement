import Companion.AreaEstimate
import Mathlib.Data.List.Rotate

namespace Companion
noncomputable section
variable {G : Type*} [Group G]

theorem prod_rotate_conjugate (xs : List G) (k : Nat) :
    (xs.rotate k).prod=(xs.take (k%xs.length)).prod⁻¹*xs.prod*(xs.take (k%xs.length)).prod := by
  have hs : xs.prod=(xs.take (k%xs.length)).prod*(xs.drop (k%xs.length)).prod := by
    rw [← List.prod_append,List.take_append_drop]
  rw [List.rotate_eq_drop_append_take_mod,List.prod_append,hs]
  group

theorem phase_prod_rotate_conjugate (xs : List G) (k : Nat) (j : G)
    (hc : ∀ x ∈ xs, Commute j x) :
    j*(xs.rotate k).prod=(xs.take (k%xs.length)).prod⁻¹*(j*xs.prod)*(xs.take (k%xs.length)).prod := by
  let q := (xs.take (k%xs.length)).prod
  have hq : Commute j q := Commute.list_prod_right _ _ (fun x hx => hc x (List.mem_of_mem_take hx))
  have hj : q⁻¹*j*q=j := by
    rw [← hq.inv_right.eq]
    group
  rw [prod_rotate_conjugate]
  change j*(q⁻¹*xs.prod*q)=q⁻¹*(j*xs.prod)*q
  calc
    _=(q⁻¹*j*q)*(q⁻¹*xs.prod*q) := by rw [hj]
    _=_ := by group

theorem phase_prod_rotate_length (L : InvariantLength G) (xs : List G) (k : Nat) (j : G)
    (hc : ∀ x ∈ xs, Commute j x) :
    L.value (j*(xs.rotate k).prod)=L.value (j*xs.prod) := by
  rw [phase_prod_rotate_conjugate xs k j hc]
  simpa only [inv_inv] using L.conjugate (xs.take (k%xs.length)).prod⁻¹ (j*xs.prod)

end
end Companion
