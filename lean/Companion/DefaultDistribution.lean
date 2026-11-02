import Companion.ProfileQuadraticInfimum
import Companion.Construction

namespace Companion.Analytic.MainProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 600000

theorem bounded_row_card {n : Nat} (L : List Nat) (hN : L.Nodup) (hB : ∀ j∈L, j<n) :
    (Finset.univ.filter (fun j : Fin n => j.val∈L)).card=L.length := by
  have he : (Finset.univ.filter (fun j : Fin n => j.val∈L)).image Fin.val=L.toFinset := by
    ext j
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact hk
    · intro hj
      exact ⟨⟨j,hB j hj⟩,hj,rfl⟩
  have hc := Finset.card_image_of_injective (Finset.univ.filter (fun j : Fin n => j.val∈L)) Fin.val_injective
  rw [he,List.toFinset_card_of_nodup hN] at hc
  exact hc.symm

def defaultPi (G : Game) (i : Fin G.equations.length) (j : Fin G.n) : ℝ :=
  if j.val∈(G.equations[i.val]).vars then 1/((G.equations.length:ℝ)*(G.equations[i.val]).vars.length) else 0

theorem defaultPi_nonneg (G : Game) (i : Fin G.equations.length) (j : Fin G.n) :
    0≤defaultPi G i j := by unfold defaultPi; split <;> positivity

theorem defaultPi_row_sum (G : Game)
    (hN : ∀ r∈G.equations, r.vars.Nodup) (hB : ∀ r∈G.equations, ∀ j∈r.vars, j<G.n)
    (hE : ∀ r∈G.equations, r.vars≠[]) (hG : G.equations≠[]) (i : Fin G.equations.length) :
    (∑ j, defaultPi G i j)=1/(G.equations.length:ℝ) := by
  have hr := List.getElem_mem i.isLt
  have hp : (0:ℝ)<(G.equations[i.val]).vars.length := by exact_mod_cast List.length_pos_iff.mpr (hE _ hr)
  have hm : (0:ℝ)<G.equations.length := by exact_mod_cast List.length_pos_iff.mpr hG
  simp only [defaultPi,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,bounded_row_card _ (hN _ hr) (hB _ hr)]
  field_simp

theorem defaultPi_normalized (G : Game)
    (hN : ∀ r∈G.equations, r.vars.Nodup) (hB : ∀ r∈G.equations, ∀ j∈r.vars, j<G.n)
    (hE : ∀ r∈G.equations, r.vars≠[]) (hG : G.equations≠[]) :
    (∑ i, ∑ j, defaultPi G i j)=1 := by
  simp_rw [defaultPi_row_sum G hN hB hE hG]
  have hm : (0:ℝ)<G.equations.length := by exact_mod_cast List.length_pos_iff.mpr hG
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

def defaultLCS (G : Game)
    (hE : ∀ r∈G.equations, r.vars≠[]) (hN : ∀ r∈G.equations, r.vars.Nodup)
    (hS : ∀ r∈G.equations, r.vars.Pairwise (· < ·))
    (hB : ∀ r∈G.equations, ∀ j∈r.vars, j<G.n) (hG : G.equations≠[])
    (s : Nat) (hU : ∀ r∈G.equations, r.vars.length≤s)
    (hA : ∃ r∈G.equations, r.vars.length=s) : LCS := by
  have hm : (0:ℝ)<G.equations.length := by exact_mod_cast List.length_pos_iff.mpr hG
  have hs : (0:ℝ)<s := by
    obtain ⟨r,hr,he⟩ := hA
    have hp := List.length_pos_iff.mpr (hE r hr)
    exact_mod_cast (show 0<s by omega)
  refine {
    system := G
    rows_nonempty := hE
    rows_nodup := hN
    rows_sorted := hS
    rows_bounded := hB
    rows_exist := hG
    pi := defaultPi G
    pi_nonneg := defaultPi_nonneg G
    pi_normalized := defaultPi_normalized G hN hB hE hG
    piMin := 1/((G.equations.length:ℝ)*s)
    piMin_pos := one_div_pos.mpr (mul_pos hm hs)
    piMin_lower := ?_
    piMin_attained := ?_
    arity := s
    arity_upper := hU
    arity_attained := hA }
  · intro i j hj
    rw [defaultPi,ite_eq_left hj]
    have hp : (0:ℝ)<(G.equations[i.val]).vars.length := by
      exact_mod_cast List.length_pos_iff.mpr (hE _ (List.getElem_mem i.isLt))
    apply one_div_le_one_div_of_le (mul_pos hm hp)
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hU _ (List.getElem_mem i.isLt))) hm.le
  · obtain ⟨r,hr,hlen⟩ := hA
    obtain ⟨k,hk,hkr⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨j,hj⟩ := List.exists_mem_of_ne_nil r.vars (hE r hr)
    refine ⟨⟨k,hk⟩,⟨j,hB r hr j hj⟩,?_,?_⟩
    · simpa only [hkr] using hj
    · simp only [defaultPi,hkr,hj,↓reduceIte,hlen]

end
end Companion.Analytic.MainProof
