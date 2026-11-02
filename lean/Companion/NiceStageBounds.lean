import Companion.GadgetBounds
set_option maxHeartbeats 500000

namespace Companion.GeneralGadget
noncomputable section
open DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

structure NiceApprox (p : Input) (gamma : Nice p → U α) (eps : ℝ) : Prop where
  square : ∀ a, defect (gamma a*gamma a)≤eps
  conjugacy : ∀ t, let (a,b,c) := niceTriple p t
    defect (gamma a*gamma b*gamma a*(gamma c)⁻¹)≤eps
  product : ∀ e, defect ((if (niceEquation p e).rhs then ScalarPhase.minusOne α else 1)*
    ((niceEquation p e).vars.map gamma).prod)≤eps
  commutation : ∀ e a b, a ∈ (niceEquation p e).vars → b ∈ (niceEquation p e).vars →
    defect (commWord (gamma a) (gamma b))≤2*eps
  nice_commutation : ∀ t, let (_,b,c) := niceTriple p t; Commute (gamma b) (gamma c)

theorem phase_product_commute (A B : U α) (h : A*B=ScalarPhase.minusOne α) : Commute A B := by
  change A*B=B*A
  have hc := (ScalarPhase.central A).eq
  calc
    A*B = ScalarPhase.minusOne α := h
    _ = A⁻¹*((A*B)*A) := by rw [h,← hc]; simp
    _ = B*A := by group

theorem thirdStage_new_commutation (p : Input) (gamma : Host p → U α) (eps : ℝ)
    (h : HostApprox p gamma eps) (e : BaseEquation p) (hne : ∀ i, e≠Sum.inl i)
    (a b : Nice p) (ha : a ∈ (niceEquation p e).vars) (hb : b ∈ (niceEquation p e).vars) :
    Commute (thirdStage p gamma a) (thirdStage p gamma b) := by
  rcases e with i|e
  · exact False.elim (hne i rfl)
  · rcases e with u|e
    · have hcomm := phase_product_commute _ _ h.distinguished
      have hc : Commute (thirdStage p gamma (nOld (hOld p.distinguished)))
          (thirdStage p gamma (nOld (hU p))) := by
        change DoubleMatrix.copy (gamma (hOld p.distinguished))*DoubleMatrix.copy (gamma (hU p))=
          DoubleMatrix.copy (gamma (hU p))*DoubleMatrix.copy (gamma (hOld p.distinguished))
        rw [← map_mul,← map_mul,hcomm.eq]
      simp [niceEquation] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      all_goals first | exact Commute.refl _ | exact hc | exact hc.symm
    · rcases e with ⟨v,k⟩|⟨t,k⟩
      · cases k
        all_goals simp [niceEquation] at ha hb
        all_goals rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
        all_goals change _*_= _*_
        all_goals simp [thirdStage,nOld,nPrime,nDPrime,nG,nBar,mono_mul,mul_assoc]
      · rcases ht : hostTriple p t with ⟨x,y,z⟩
        cases k
        all_goals simp [niceEquation,ht] at ha hb
        all_goals rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
        all_goals change _*_= _*_
        all_goals simp [thirdStage,nPrime,nDPrime,nK,ht,mono_mul,mul_assoc]

theorem thirdStage_approx (p : Input) (gamma : Host p → U α) (hc : 0<Fintype.card α)
    (eps : ℝ) (he : 0≤eps) (h : HostApprox p gamma eps) :
    NiceApprox p (thirdStage p gamma) eps := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a
    rcases a with ⟨k,a⟩|a
    · fin_cases k
      · simpa [thirdStage,mono_mul] using diagonal_bound hc (gamma a*gamma a) (gamma a*gamma a) eps he (h.square a) (h.square a)
      · simpa [thirdStage,mono_mul,DoubleMatrix.first] using first_bound hc (gamma a*gamma a) eps he (h.square a)
      · simpa [thirdStage,mono_mul] using second_bound hc (gamma a*gamma a) eps he (h.square a)
      · simpa [thirdStage,mono_mul] using diagonal_bound hc (gamma a*gamma a) (gamma a*gamma a) eps he (h.square a) (h.square a)
    · rcases a with u|⟨t,k⟩
      · simpa [thirdStage,ScalarPhase.swap_square,defect_one] using he
      · rcases ht : hostTriple p t with ⟨a,b,c⟩
        cases k
        · simpa [thirdStage,ht,mono_mul] using diagonal_bound hc (gamma b*gamma b) (gamma c*gamma c) eps he (h.square b) (h.square c)
        · simpa [thirdStage,ht,mono_mul] using diagonal_bound hc (gamma c*gamma c) (gamma b*gamma b) eps he (h.square c) (h.square b)
  · intro t
    rcases t with a|⟨t,k⟩
    · simpa [niceTriple,thirdStage,nG,nPrime,nDPrime,swap,mono_mul,mono_inv,mul_assoc,mono_one,defect_one] using he
    · rcases ht : hostTriple p t with ⟨a,b,c⟩
      have hrel : defect (gamma a*gamma b*gamma a*(gamma c)⁻¹)≤eps := by simpa [ht] using h.conjugacy t
      cases k
      · simpa [niceTriple,thirdStage,ht,nBar,nPrime,nDPrime,mono_mul,mono_inv,mul_assoc] using
          diagonal_bound hc (gamma a*gamma a) (gamma a*gamma b*gamma a*(gamma c)⁻¹) eps he (h.square a) hrel
      · simpa [niceTriple,thirdStage,ht,nBar,nPrime,nDPrime,mono_mul,mono_inv,mul_assoc] using
          diagonal_bound hc (gamma a*gamma b*gamma a*(gamma c)⁻¹) (gamma a*gamma a) eps he hrel (h.square a)
  · intro e
    rcases e with i|e
    · have hb := copy_bound hc _ eps he (h.linear i)
      simpa [niceEquation,thirdStage,nOld,DoubleMatrix.copy,map_list_prod,List.map_map,Function.comp_def] using hb
    · rcases e with u|e
      · have heq : ScalarPhase.minusOne (Bool × α)*
            (thirdStage p gamma (nOld (hOld p.distinguished))*thirdStage p gamma (nOld (hU p)))=1 := by
          change ScalarPhase.minusOne (Bool × α)*
            (DoubleMatrix.copy (gamma (hOld p.distinguished))*DoubleMatrix.copy (gamma (hU p)))=1
          rw [← map_mul,h.distinguished,ScalarPhase.copy,ScalarPhase.square]
        simpa [niceEquation,heq,defect_one] using he
      · rcases e with ⟨a,k⟩|⟨t,k⟩
        · cases k
          all_goals simpa [niceEquation,thirdStage,nOld,nPrime,nDPrime,nG,nBar,swap,mono_mul,mul_assoc] using
            diagonal_bound hc (gamma a*gamma a) (gamma a*gamma a) eps he (h.square a) (h.square a)
        · rcases ht : hostTriple p t with ⟨a,b,c⟩
          cases k
          · simpa [niceEquation,thirdStage,ht,nPrime,nDPrime,nK,mono_mul,mul_assoc] using
              diagonal_bound hc (gamma b*gamma b) (gamma c*gamma c) eps he (h.square b) (h.square c)
          · simpa [niceEquation,thirdStage,ht,nPrime,nDPrime,nK,mono_mul,mul_assoc] using
              diagonal_bound hc (gamma c*gamma c) (gamma b*gamma b) eps he (h.square c) (h.square b)
  · intro e a b ha hb
    rcases e with i|e
    · have ha' : a ∈ (p.linear[i]).map (fun v => nOld (hOld v)) := by simpa [niceEquation] using ha
      have hb' : b ∈ (p.linear[i]).map (fun v => nOld (hOld v)) := by simpa [niceEquation] using hb
      obtain ⟨aa,haa,rfl⟩ := List.mem_map.mp ha'
      obtain ⟨bb,hbb,rfl⟩ := List.mem_map.mp hb'
      have hh := copy_bound hc _ (2*eps) (by positivity) (h.linear_commutation i aa haa bb hbb)
      simpa [commWord,thirdStage,nOld,DoubleMatrix.copy,mono_mul,mono_inv,mul_assoc] using hh
    · have hh := thirdStage_new_commutation p gamma eps h (.inr e) (by intro i; simp) a b ha hb
      have heq : commWord (thirdStage p gamma a) (thirdStage p gamma b)=1 := by
        unfold commWord
        rw [hh.eq]
        simp [mul_assoc]
      rw [heq,defect_one]
      positivity
  · intro t
    rcases t with a|⟨t,k⟩
    · exact thirdStage_new_commutation p gamma eps h (.inr (.inr (.inl (a,false))))
        (by intro i; simp) _ _ (by simp [niceEquation,niceTriple]) (by simp [niceEquation,niceTriple])
    · rcases ht : hostTriple p t with ⟨a,b,c⟩
      cases k
      · simpa [niceTriple,ht] using thirdStage_new_commutation p gamma eps h (.inr (.inr (.inr (t,false))))
          (by intro i; simp) (nPrime b) (nDPrime c) (by simp [niceEquation,ht]) (by simp [niceEquation,ht])
      · simpa [niceTriple,ht] using thirdStage_new_commutation p gamma eps h (.inr (.inr (.inr (t,true))))
          (by intro i; simp) (nDPrime b) (nPrime c) (by simp [niceEquation,ht]) (by simp [niceEquation,ht])

end
end Companion.GeneralGadget
