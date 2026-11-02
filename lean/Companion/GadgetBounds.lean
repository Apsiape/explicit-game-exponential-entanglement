import Companion.GlobalGadgetAssignment
import Mathlib.Tactic.Group
set_option maxHeartbeats 1000000

namespace Companion.GeneralGadget
noncomputable section
open DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

def commWord {G : Type} [Group G] (A B : G) : G := A*B*A⁻¹*B⁻¹
theorem commWord_reverse {G : Type} [Group G] (A B : G) : commWord B A=(commWord A B)⁻¹ := by
  simp only [commWord,mul_inv_rev,inv_inv]
  group
theorem commutation_cost {G : Type} [Group G] (L : InvariantLength G) (A B : G) (eps : ℝ)
    (hA : L.value (A*A)≤eps) (hconj : L.value (A*B*A*B⁻¹)≤eps) :
    L.value (commWord A B)≤2*eps := by
  have he : commWord A B=(A*B*A*B⁻¹)*(B*(A*A)⁻¹*B⁻¹) := by unfold commWord; group
  rw [he]
  calc
    _ ≤ L.value (A*B*A*B⁻¹)+L.value (B*(A*A)⁻¹*B⁻¹) := L.mul_le _ _
    _ = L.value (A*B*A*B⁻¹)+L.value (A*A) := by rw [L.conjugate,L.inv]
    _ ≤ 2*eps := by linarith

theorem first_bound (hc : 0<Fintype.card α) (A : U α) (eps : ℝ) (he : 0≤eps)
    (ha : defect A≤eps) : defect (first A)≤eps :=
  diagonal_bound hc A 1 eps he ha (by simpa [defect_one] using he)
theorem second_bound (hc : 0<Fintype.card α) (A : U α) (eps : ℝ) (he : 0≤eps)
    (ha : defect A≤eps) : defect (diag 1 A)≤eps :=
  diagonal_bound hc 1 A eps he (by simpa [defect_one] using he) ha
theorem copy_bound (hc : 0<Fintype.card α) (A : U α) (eps : ℝ) (he : 0≤eps)
    (ha : defect A≤eps) : defect (DoubleMatrix.copy A)≤eps :=
  diagonal_bound hc A A eps he ha ha

structure HostApprox (p : Input) (gamma : Host p → U α) (eps : ℝ) : Prop where
  square : ∀ a, defect (gamma a*gamma a)≤eps
  conjugacy : ∀ t, let (a,b,c) := hostTriple p t
    defect (gamma a*gamma b*gamma a*(gamma c)⁻¹)≤eps
  linear : ∀ i : Fin p.linear.length, defect (((p.linear[i]).map (fun a => gamma (hOld a))).prod)≤eps
  linear_commutation : ∀ i : Fin p.linear.length, ∀ a ∈ p.linear[i], ∀ b ∈ p.linear[i],
    defect (commWord (gamma (hOld a)) (gamma (hOld b)))≤2*eps
  distinguished : gamma (hOld p.distinguished)*gamma (hU p)=ScalarPhase.minusOne α

theorem firstStage_approx (p : Input) (phi : FreeGroup (Source p) →* U α) (hc : 0<Fintype.card α)
    (eps : ℝ) (he : 0≤eps)
    (hr : ∀ i, defect (phi (sourceRelator p i))≤eps)
    (hw : phi (srcOld p.distinguished)=ScalarPhase.minusOne α) :
    HostApprox p (firstStage p phi) eps := by
  let A := fun a => phi (srcOld a)
  let Y := fun a => phi (srcY a)
  have hsq (a : Fin p.n0) : defect (A a*A a)≤eps := by
    simpa [A,sourceRelator] using hr (.inl a)
  have hconj (i : Fin p.c0.length) :
      let (a,b,c) := p.c0[i]; defect (A a*A b*A a*(A c)⁻¹)≤eps := by
    simpa [A,sourceRelator] using hr (.inr (.inr (.inl i)))
  have hYconj (i : Fin p.c1.length) :
      defect (Y (p.yIndex i)*A (p.c1[i]).1*(Y (p.yIndex i))⁻¹*(A (p.c1[i]).2)⁻¹)≤eps := by
    simpa [A,Y,sourceRelator] using hr (.inr (.inr (.inr i)))
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a
    rcases a with a|a
    · simpa [firstStage,mono_mul,DoubleMatrix.first,A] using first_bound hc (A a*A a) eps he (hsq a)
    · rcases a with a|a
      · simp [firstStage,ScalarPhase.swap_square,defect_one,he]
      · rcases a with a|a
        · simpa [firstStage,mono_mul,mono_one,mul_assoc,defect_one] using he
        · rcases a with i|b
          · let Z := Y (p.yIndex i)*A (p.c1[i]).1*(Y (p.yIndex i))⁻¹
            have hz : defect (Z*Z)≤eps := by
              have heq : Z*Z=Y (p.yIndex i)*(A (p.c1[i]).1*A (p.c1[i]).1)*(Y (p.yIndex i))⁻¹ := by
                dsimp [Z]; group
              rw [heq]
              change (DoubleMatrix.length (α:=α)).value _≤eps
              rw [InvariantLength.conjugate]
              exact hsq _
            simpa [firstStage,mono_mul,Z,Y,A] using second_bound hc (Z*Z) eps he hz
          · cases b
            · simpa [firstStage,ScalarPhase.swap_square,defect_one] using he
            · simpa [firstStage,ScalarPhase.u_square,defect_one] using he
  · intro t
    rcases t with i|t
    · have h := first_bound hc _ eps he (hconj i)
      simpa [hostTriple,firstStage,hOld,DoubleMatrix.first,mono_mul,mono_inv,A,mul_assoc] using h
    · rcases t with ⟨i,b⟩|u
      · cases b
        · simpa [hostTriple,firstStage,hF,hV,hZ,hOld,mono_mul,mono_inv,mul_assoc,mono_one,defect_one] using he
        · have h := first_bound hc _ eps he (hYconj i)
          simpa [hostTriple,firstStage,hF,hV,hZ,hOld,DoubleMatrix.first,mono_mul,mono_inv,A,Y,mul_assoc] using h
      · have h := step2_conjugacy p phi hw
        simpa [hostTriple,h,defect_one] using he
  · intro i
    have hsource : defect (((p.linear[i]).map A).prod)≤eps := by
      simpa [sourceRelator,map_list_prod,List.map_map,A,Function.comp_def] using hr (.inr (.inl i))
    have hb := first_bound hc _ eps he hsource
    simpa [firstStage,hOld,DoubleMatrix.first,map_list_prod,List.map_map,A,Function.comp_def] using hb
  · intro i a ha b hb
    have hsource : defect (commWord (A a) (A b))≤2*eps := by
      by_cases hab : a=b
      · subst b; simpa [commWord,defect_one] using (mul_nonneg (by norm_num : (0:ℝ)≤2) he)
      · rcases p.linear_commutations i a ha b hb hab with hm|hm
        · obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hm
          have hh : defect (A a*A b*A a*(A b)⁻¹)≤eps := by
            have ht := hconj ⟨j,hj⟩
            change defect (A (p.c0[j]).1*A (p.c0[j]).2.1*A (p.c0[j]).1*(A (p.c0[j]).2.2)⁻¹)≤eps at ht
            rw [hget] at ht
            exact ht
          exact commutation_cost (DoubleMatrix.length (α:=α)) _ _ eps (hsq a) hh
        · obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hm
          have hh : defect (A b*A a*A b*(A a)⁻¹)≤eps := by
            have ht := hconj ⟨j,hj⟩
            change defect (A (p.c0[j]).1*A (p.c0[j]).2.1*A (p.c0[j]).1*(A (p.c0[j]).2.2)⁻¹)≤eps at ht
            rw [hget] at ht
            exact ht
          have hg := commutation_cost (DoubleMatrix.length (α:=α)) _ _ eps (hsq b) hh
          rw [commWord_reverse]
          change (DoubleMatrix.length (α:=α)).value _≤_
          rw [InvariantLength.inv]
          exact hg
    have hd := first_bound hc _ (2*eps) (by positivity) hsource
    simpa [commWord,firstStage,hOld,DoubleMatrix.first,mono_mul,mono_inv,A,mul_assoc] using hd
  · simpa [firstStage,hOld,hU,hw] using (ScalarPhase.diagonal_product (α:=α))

end
end Companion.GeneralGadget
