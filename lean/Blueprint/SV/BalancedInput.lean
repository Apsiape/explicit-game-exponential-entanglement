import Blueprint.SV.BalancedAlgebra
import Companion.GeneralGadgetTheorem

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic Companion.DoubleMatrix

/-- The all-involutive presentation after the first two removals in Lemma 11.13.
Indices are a,b,c,f,v,Za,Zb,W,f',v',Zc,Zf,Zv. -/
def balancedInput : GeneralGadget.Input where
  n0 := 13
  hasY := false
  distinguished := 2
  c0 := [(0,1,1),(0,2,2),(1,2,2),
    (4,0,5),(3,5,1),(4,1,6),(3,6,0),(4,3,7),
    (9,2,10),(8,10,2),(9,3,11),(8,11,3),(9,4,12),(8,12,7)]
  c1 := []
  c1_absent := by simp
  linear := [[0,1,2]]
  linear_nodup := by decide
  linear_small := by decide
  linear_order := by intro i; fin_cases i; exact ⟨0,by decide⟩
  linear_commutations := by decide

theorem balancedInput_sizes :
    Fintype.card (GeneralGadget.Variable balancedInput)=406 ∧
      Fintype.card (GeneralGadget.EquationIndex balancedInput)=332 := by decide

variable {α : Type} [Fintype α] [DecidableEq α]

def balancedGenerators (A B C Y : U α) (F V : U (Bool × α)) : Fin 13 → U (Bool × α)
  | 0 => diag A 1
  | 1 => diag B 1
  | 2 => diag C 1
  | 3 => swap α
  | 4 => liftedY Y
  | 5 => firstLiftAncilla Y A
  | 6 => firstLiftAncilla Y B
  | 7 => firstLiftPower Y
  | 8 => F
  | 9 => V
  | 10 => V * diag C 1 * V
  | 11 => V * swap α * V
  | _ => V * liftedY Y * V

theorem balancedGenerators_squares (A B C Y : U α) (F V : U (Bool × α))
    (hA : A*A=1) (hB : B*B=1) (hC : C*C=1) (hF : F*F=1) (hV : V*V=1) :
    ∀ i, balancedGenerators A B C Y F V i * balancedGenerators A B C Y F V i = 1 := by
  have hAC : diag A (1:U α) * diag A 1 = 1 := by simpa [mono_mul,hA] using (mono_one (α:=α))
  have hBC : diag B (1:U α) * diag B 1 = 1 := by simpa [mono_mul,hB] using (mono_one (α:=α))
  have hCC : diag C (1:U α) * diag C 1 = 1 := by simpa [mono_mul,hC] using (mono_one (α:=α))
  intro i
  fin_cases i
  · exact hAC
  · exact hBC
  · exact hCC
  · exact ScalarPhase.swap_square
  · exact liftedY_square Y
  · exact conjugate_square _ _ (liftedY_square Y) hAC
  · exact conjugate_square _ _ (liftedY_square Y) hBC
  · exact firstLiftPower_square Y
  · exact hF
  · exact hV
  · exact conjugate_square _ _ hV hCC
  · exact conjugate_square _ _ hV ScalarPhase.swap_square
  · exact conjugate_square _ _ hV (liftedY_square Y)

theorem balancedGenerators_linear (A B C Y : U α) (F V : U (Bool × α))
    (h : A*B*C=1) :
    ((balancedInput.linear[0]).map (balancedGenerators A B C Y F V)).prod = 1 := by
  simpa [balancedInput,balancedGenerators,mono_mul,mono_one,mul_assoc] using
    congrArg (fun R : U α => diag R 1) h

theorem balancedGenerators_conjugacy (hc : 0<Fintype.card α)
    (A B C X Y : U α) (F V : U (Bool × α))
    (hA : A*A=1) (hB : B*B=1) (hC : C*C=1)
    (hF : F*F=1) (hV : V*V=1) (hX : F*V=diag X X)
    (hAB : Commute A B) (hAC : Commute A C) (hBC : Commute B C)
    (hYA : Y*A*Y⁻¹=B) (hYB : Y*B*Y⁻¹=A) (hXC : X*C*X⁻¹=C)
    (e : ℝ) (he : 0≤e) (hR : defect (powerResidual X Y)≤e) :
    ∀ i : Fin balancedInput.c0.length,
      let (a,b,c) := balancedInput.c0[i]
      defect (balancedGenerators A B C Y F V a * balancedGenerators A B C Y F V b *
        balancedGenerators A B C Y F V a * (balancedGenerators A B C Y F V c)⁻¹) ≤ e := by
  have hswap := ScalarPhase.swap_square (α:=α)
  have hLY := liftedY_square Y
  have hAX : X*X⁻¹=1 := mul_inv_cancel X
  have hcA : A*B*A*B⁻¹=1 := by
    calc
      _ = B*(A*A)*B⁻¹ := by rw [hAB.eq]; group
      _ = 1 := by rw [hA]; group
  have hcB : A*C*A*C⁻¹=1 := by
    calc
      _ = C*(A*A)*C⁻¹ := by rw [hAC.eq]; group
      _ = 1 := by rw [hA]; group
  have hcC : B*C*B*C⁻¹=1 := by
    calc
      _ = C*(B*B)*C⁻¹ := by rw [hBC.eq]; group
      _ = 1 := by rw [hB]; group
  have hdiagC : diag X X * diag C 1 * (diag X X)⁻¹ = diag C 1 := by
    simp [mono_mul,mono_inv,mul_assoc,hXC]
  have hdiagF : diag X X * swap α * (diag X X)⁻¹ = swap α := by
    simp [mono_mul,mono_inv,swap,mul_assoc]
  intro i
  fin_cases i
  · change defect (diag A 1 * diag B 1 * diag A 1 * (diag B 1)⁻¹)≤e
    simpa [mono_mul,mono_inv,←mul_assoc,hcA,mono_one,defect_one] using he
  · change defect (diag A 1 * diag C 1 * diag A 1 * (diag C 1)⁻¹)≤e
    simpa [mono_mul,mono_inv,←mul_assoc,hcB,mono_one,defect_one] using he
  · change defect (diag B 1 * diag C 1 * diag B 1 * (diag C 1)⁻¹)≤e
    simpa [mono_mul,mono_inv,←mul_assoc,hcC,mono_one,defect_one] using he
  · change defect (liftedY Y * diag A 1 * liftedY Y * (firstLiftAncilla Y A)⁻¹)≤e
    simp only [firstLiftAncilla,mul_inv_cancel,defect_one,he]
  · change defect (swap α * firstLiftAncilla Y A * swap α * (diag B 1)⁻¹)≤e
    simpa [firstLift_conjugacy_residual,hYA,mono_one,defect_one] using he
  · change defect (liftedY Y * diag B 1 * liftedY Y * (firstLiftAncilla Y B)⁻¹)≤e
    simp only [firstLiftAncilla,mul_inv_cancel,defect_one,he]
  · change defect (swap α * firstLiftAncilla Y B * swap α * (diag A 1)⁻¹)≤e
    simpa [firstLift_conjugacy_residual,hYB,mono_one,defect_one] using he
  · change defect (liftedY Y * swap α * liftedY Y * (firstLiftPower Y)⁻¹)≤e
    simp only [firstLiftPower,mul_inv_cancel,defect_one,he]
  · change defect (V * diag C 1 * V * (V * diag C 1 * V)⁻¹)≤e
    simp only [mul_inv_cancel,defect_one,he]
  · change defect (F * (V * diag C 1 * V) * F * (diag C 1)⁻¹)≤e
    rw [split_conjugacy_residual _ _ _ _ hF hV,hX,hdiagC,mul_inv_cancel,defect_one]
    exact he
  · change defect (V * swap α * V * (V * swap α * V)⁻¹)≤e
    simp only [mul_inv_cancel,defect_one,he]
  · change defect (F * (V * swap α * V) * F * (swap α)⁻¹)≤e
    rw [split_conjugacy_residual _ _ _ _ hF hV,hX,hdiagF,mul_inv_cancel,defect_one]
    exact he
  · change defect (V * liftedY Y * V * (V * liftedY Y * V)⁻¹)≤e
    simp only [mul_inv_cancel,defect_one,he]
  · change defect (F * (V * liftedY Y * V) * F * (firstLiftPower Y)⁻¹)≤e
    rw [split_conjugacy_residual _ _ _ _ hF hV,hX]
    exact firstLift_power_bound hc X Y e he hR

def balancedHost (A B C Y : U α) (F V : U (Bool × α)) :
    GeneralGadget.Host balancedInput → U (Bool × α)
  | .inl a => balancedGenerators A B C Y F V a
  | .inr (.inl a) => Fin.elim0 a
  | .inr (.inr (.inl a)) => Fin.elim0 a
  | .inr (.inr (.inr (.inl a))) => Fin.elim0 a
  | .inr (.inr (.inr (.inr false))) => swap α
  | .inr (.inr (.inr (.inr true))) => diag 1 (ScalarPhase.minusOne α)

theorem balancedHost_approx (hc : 0<Fintype.card α)
    (A B C X Y : U α) (F V : U (Bool × α))
    (hA : A*A=1) (hB : B*B=1) (hC : C=ScalarPhase.minusOne α)
    (hF : F*F=1) (hV : V*V=1) (hX : F*V=diag X X)
    (hAB : Commute A B) (hYA : Y*A*Y⁻¹=B) (hYB : Y*B*Y⁻¹=A)
    (hlin : A*B*C=1) (e : ℝ) (he : 0≤e) (hR : defect (powerResidual X Y)≤e) :
    GeneralGadget.HostApprox balancedInput (balancedHost A B C Y F V) e := by
  have hC2 : C*C=1 := by rw [hC]; exact ScalarPhase.square
  have hAC : Commute A C := by rw [hC]; exact ScalarPhase.central A
  have hBC : Commute B C := by rw [hC]; exact ScalarPhase.central B
  have hXC : X*C*X⁻¹=C := by rw [(show Commute X C by rw [hC]; exact ScalarPhase.central X).eq]; group
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a
    rcases a with a|a|a|a|b
    · change defect (balancedGenerators A B C Y F V a * balancedGenerators A B C Y F V a)≤e
      rw [balancedGenerators_squares A B C Y F V hA hB hC2 hF hV a,defect_one]
      exact he
    · exact Fin.elim0 a
    · exact Fin.elim0 a
    · exact Fin.elim0 a
    · cases b
      · simpa [balancedHost,ScalarPhase.swap_square,defect_one] using he
      · simpa [balancedHost,ScalarPhase.u_square,defect_one] using he
  · intro t
    rcases t with i|⟨i,b⟩|u
    · simpa only [GeneralGadget.hostTriple,balancedHost,GeneralGadget.hOld] using
        balancedGenerators_conjugacy hc A B C X Y F V hA hB hC2 hF hV hX
          hAB hAC hBC hYA hYB hXC e he hR i
    · exact Fin.elim0 i
    · simpa [GeneralGadget.hostTriple,GeneralGadget.hT,GeneralGadget.hOld,GeneralGadget.hU,
        balancedHost,balancedInput,balancedGenerators,hC,ScalarPhase.switch,
        mul_inv_cancel,defect_one] using he
  · intro i
    fin_cases i
    change defect (diag A 1 * (diag B 1 * (diag C 1 * 1)))≤e
    simpa [mono_mul,←mul_assoc,hlin,mono_one,defect_one] using he
  · intro i a ha b hb
    fin_cases i
    change a∈([0,1,2]:List (Fin 13)) at ha
    change b∈([0,1,2]:List (Fin 13)) at hb
    have mem3 (x : Fin 13) (h : x∈([0,1,2]:List (Fin 13))) : x=0 ∨ x=1 ∨ x=2 := by
      rcases List.mem_cons.mp h with h|h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h|h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (List.mem_singleton.mp h))
    have ha' := mem3 a ha
    have hb' := mem3 b hb
    have hc' : Commute (balancedHost A B C Y F V (GeneralGadget.hOld a))
        (balancedHost A B C Y F V (GeneralGadget.hOld b)) := by
      have hab := hAB.map (DoubleMatrix.first (α:=α))
      have hac := hAC.map (DoubleMatrix.first (α:=α))
      have hbc := hBC.map (DoubleMatrix.first (α:=α))
      rcases ha' with rfl|rfl|rfl <;> rcases hb' with rfl|rfl|rfl
      all_goals first
        | exact Commute.refl _
        | exact hab
        | exact hab.symm
        | exact hac
        | exact hac.symm
        | exact hbc
        | exact hbc.symm
    have hh : GeneralGadget.commWord
        (balancedHost A B C Y F V (GeneralGadget.hOld a))
        (balancedHost A B C Y F V (GeneralGadget.hOld b)) = 1 := by
      rw [GeneralGadget.commWord,hc'.eq]
      group
    rw [hh,defect_one]
    linarith
  · simp [GeneralGadget.hOld,GeneralGadget.hU,balancedHost,balancedInput,balancedGenerators,hC,
      ScalarPhase.diagonal_product]

/-- The last two checked gadget stages complete the balanced lift in dimension 8d.
This is the presentation-level part of Lemma 11.13, before numeric LCS encoding. -/
theorem balanced_solution_lift (hc : 0<Fintype.card α)
    (A B C X Y : U α) (F V : U (Bool × α))
    (hA : A*A=1) (hB : B*B=1) (hC : C=ScalarPhase.minusOne α)
    (hF : F*F=1) (hV : V*V=1) (hX : F*V=diag X X)
    (hAB : Commute A B) (hYA : Y*A*Y⁻¹=B) (hYB : Y*B*Y⁻¹=A)
    (hlin : A*B*C=1) (e : ℝ) (he : 0≤e) (hR : defect (powerResidual X Y)≤e) :
    ∃ phi : FreeGroup (Option (GeneralGadget.Variable balancedInput)) →*
        U (Bool × (Bool × (Bool × α))),
      (∀ i, defect (phi (GeneralGadget.solutionRelator balancedInput i))≤3*e) ∧
      phi (FreeGroup.of none)=ScalarPhase.minusOne _ ∧
      Fintype.card (Bool × (Bool × (Bool × α)))=8*Fintype.card α := by
  let gamma := balancedHost A B C Y F V
  have hg := balancedHost_approx hc A B C X Y F V hA hB hC hF hV hX hAB hYA hYB hlin e he hR
  have hpos : 0<Fintype.card (Bool × α) := by simp; omega
  have hn := GeneralGadget.thirdStage_approx balancedInput gamma hpos e he hg
  have hpos' : 0<Fintype.card (Bool × (Bool × α)) := by simp; omega
  refine ⟨GeneralGadget.finalStageHom balancedInput (GeneralGadget.thirdStage balancedInput gamma),
    GeneralGadget.fourthStage_approx _ _ hpos' e he hn,GeneralGadget.final_phase _ _,?_⟩
  simp
  omega

end
end Blueprint.SV

#print axioms Blueprint.SV.balancedInput
#print axioms Blueprint.SV.balancedInput_sizes
#print axioms Blueprint.SV.balancedGenerators
#print axioms Blueprint.SV.balancedGenerators_squares
#print axioms Blueprint.SV.balancedGenerators_linear
#print axioms Blueprint.SV.balancedGenerators_conjugacy
#print axioms Blueprint.SV.balancedHost
#print axioms Blueprint.SV.balancedHost_approx
#print axioms Blueprint.SV.balanced_solution_lift
