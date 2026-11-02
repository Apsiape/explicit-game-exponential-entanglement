import Blueprint.SpatialDefinitions
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace Blueprint.SpatialProof
noncomputable section
open Companion Companion.Analytic
open scoped TensorProduct
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem positive_iff (A : E →L[ℂ] E) :
    positiveOperator A ↔ A.IsPositive := by
  constructor
  · intro h
    refine ⟨h.1,fun x => ?_⟩
    change 0≤(inner ℂ (A x) x).re
    rw [h.1 x x]
    exact h.2 x
  · intro h
    exact ⟨h.1,fun x => h.re_inner_nonneg_right x⟩

theorem tensor_adjoint_identity [CompleteSpace E] [CompleteSpace F]
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (x y : E ⊗[ℂ] F) :
    inner ℂ x (TensorProduct.mapL A B y)=
      inner ℂ (TensorProduct.mapL A.adjoint B.adjoint x) y := by
  induction x using TensorProduct.inductionOn with
  | tmul x₁ x₂ =>
    induction y using TensorProduct.inductionOn with
    | tmul y₁ y₂ =>
      simp only [TensorProduct.mapL_tmul,TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_left]
    | add y z hy hz => simp only [map_add,inner_add_right,hy,hz]
  | add x z hx hz => simp only [map_add,inner_add_left,hx,hz]

theorem tensor_expectation_nonneg [CompleteSpace E] [CompleteSpace F]
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (hA : positiveOperator A) (hB : positiveOperator B)
    (psi : SpatialTensor E F) :
    0≤(inner ℂ psi (UniformSpace.Completion.map (TensorProduct.mapL A B) psi)).re := by
  have ha : 0≤A := ContinuousLinearMap.nonneg_iff_isPositive.mpr ((positive_iff A).mp hA)
  have hb : 0≤B := ContinuousLinearMap.nonneg_iff_isPositive.mpr ((positive_iff B).mp hB)
  let S := CFC.sqrt A
  let T := CFC.sqrt B
  have hS : S.adjoint=S := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hT : T.adjoint=T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)
  have hs : S*S=A := CFC.sqrt_mul_sqrt_self A ha
  have ht : T*T=B := CFC.sqrt_mul_sqrt_self B hb
  induction psi using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le continuous_const (by fun_prop)
  | ih x =>
    rw [UniformSpace.Completion.map_coe (TensorProduct.mapL A B).uniformContinuous,
      UniformSpace.Completion.inner_coe]
    rw [←hs,←ht,TensorProduct.mapL_mul,mul_apply_eq_comp,
      tensor_adjoint_identity,hS,hT]
    simpa using (inner_self_nonneg (𝕜:=ℂ) (x:=TensorProduct.mapL S T x))

theorem completion_add (A B : E →L[ℂ] E) :
    (A+B).completion=A.completion+B.completion := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp [←UniformSpace.Completion.coe_add]

theorem completion_id :
    (ContinuousLinearMap.id ℂ E).completion=ContinuousLinearMap.id ℂ _ := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp

def expect (psi : SpatialTensor E F) (A : E →L[ℂ] E) (B : F →L[ℂ] F) : ℝ :=
  (inner ℂ psi ((TensorProduct.mapL A B).completion psi)).re

theorem expect_add_left (psi : SpatialTensor E F) (A C : E →L[ℂ] E) (B : F →L[ℂ] F) :
    expect psi (A+C) B=expect psi A B+expect psi C B := by
  simp only [expect,TensorProduct.mapL_add_left,completion_add,add_apply,
    inner_add_right,Complex.add_re]

theorem expect_add_right (psi : SpatialTensor E F) (A : E →L[ℂ] E) (B C : F →L[ℂ] F) :
    expect psi A (B+C)=expect psi A B+expect psi A C := by
  simp only [expect,TensorProduct.mapL_add_right,completion_add,add_apply,
    inner_add_right,Complex.add_re]

theorem expect_zero_left (psi : SpatialTensor E F) (B : F →L[ℂ] F) :
    expect psi 0 B=0 := by
  simp only [expect,TensorProduct.mapL_zero_left]
  have hz : (0 : E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F).completion=0 := by
    ext x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp
  simp [hz]

theorem expect_sum_left {I : Type*} (S : Finset I) (psi : SpatialTensor E F)
    (A : I → E →L[ℂ] E) (B : F →L[ℂ] F) :
    expect psi (∑ a∈S, A a) B=∑ a∈S, expect psi (A a) B := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [expect_zero_left]
  | @insert a S ha ih => simp [Finset.sum_insert,ha,expect_add_left,ih]

theorem expect_id (psi : SpatialTensor E F) :
    expect psi (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ F)=‖psi‖^2 := by
  simp only [expect,TensorProduct.mapL_id_id,completion_id,ContinuousLinearMap.id_apply]
  simpa using (inner_self_eq_norm_sq (𝕜:=ℂ) psi)

theorem matching_probability_le_one [CompleteSpace E] [CompleteSpace F]
    {I : Type*} [Fintype I] (psi : SpatialTensor E F) (A : I → E →L[ℂ] E)
    (B : Bool → F →L[ℂ] F) (f : I → Bool) (hpsi : ‖psi‖=1)
    (hA : ∀ a, positiveOperator (A a)) (hB : ∀ b, positiveOperator (B b))
    (hAc : ∑ a, A a=ContinuousLinearMap.id ℂ E)
    (hBc : B true+B false=ContinuousLinearMap.id ℂ F) :
    ∑ a, expect psi (A a) (B (f a))≤1 := by
  have he a : expect psi (A a) (B (f a))≤
      expect psi (A a) (B true)+expect psi (A a) (B false) := by
    have ht := tensor_expectation_nonneg (A a) (B true) (hA a) (hB true) psi
    have hf := tensor_expectation_nonneg (A a) (B false) (hA a) (hB false) psi
    change 0≤expect psi (A a) (B true) at ht
    change 0≤expect psi (A a) (B false) at hf
    cases f a <;> linarith
  calc
    _≤∑ a, (expect psi (A a) (B true)+expect psi (A a) (B false)) :=
      Finset.sum_le_sum (fun a _ => he a)
    _=expect psi (∑ a, A a) (B true+B false) := by
      rw [expect_sum_left]
      simp_rw [expect_add_right]
    _=1 := by rw [hAc,hBc,expect_id,hpsi]; norm_num

def pairScore (g : LCS) (psi : SpatialTensor E F)
    (A : Fin g.system.equations.length → (Fin g.system.n → Bool) → E →L[ℂ] E)
    (B : Fin g.system.n → Bool → F →L[ℂ] F)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) : ℝ :=
  if j.val∈(g.system.equations[i.val]).vars then
    ∑ a, expect psi (A i a) (B j (a j)) else 1

theorem pair_score_le_one [CompleteSpace E] [CompleteSpace F]
    (g : LCS) (psi : SpatialTensor E F) A B (hpsi : ‖psi‖=1)
    (hv : validSpatial g A B) (i : Fin g.system.equations.length) (j : Fin g.system.n) :
    pairScore g psi A B i j≤1 := by
  unfold pairScore
  split
  · exact matching_probability_le_one psi (A i) (B j) (fun a => a j) hpsi
      (hv.1 i) (hv.2.2.2.1 j) (hv.2.1 i) (hv.2.2.2.2 j)
  · rfl

theorem weighted_average_one {I J : Type*} [Fintype I] [Fintype J]
    (p q : I → J → ℝ) (hp : ∀ i j, 0≤p i j) (hpSum : ∑ i, ∑ j, p i j=1)
    (hq : ∀ i j, q i j≤1) (hscore : ∑ i, ∑ j, p i j*q i j=1)
    (i : I) (j : J) (hpos : 0<p i j) : q i j=1 := by
  have hn i j : 0≤p i j*(1-q i j) := mul_nonneg (hp i j) (sub_nonneg.mpr (hq i j))
  have hz : ∑ i, ∑ j, p i j*(1-q i j)=0 := by
    simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [hpSum,hscore,sub_self]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))).mp hz i (Finset.mem_univ i)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp hi j
    (Finset.mem_univ j)
  have hh := (mul_eq_zero.mp hij).resolve_left hpos.ne'
  linarith

theorem perfect_iff_pointwise [CompleteSpace E] [CompleteSpace F]
    (g : LCS) (psi : SpatialTensor E F) A B (hpsi : ‖psi‖=1)
    (hv : validSpatial g A B) :
    spatialWin g psi A B=1 ↔
      ∀ i j, j.val∈(g.system.equations[i.val]).vars →
        ∑ a, expect psi (A i a) (B j (a j))=1 := by
  constructor
  · intro hw i j hj
    have hh := weighted_average_one g.pi (pairScore g psi A B) g.pi_nonneg g.pi_normalized
      (pair_score_le_one g psi A B hpsi hv) hw i j
      (g.piMin_pos.trans_le (g.piMin_lower i j hj))
    simpa only [pairScore,hj,↓reduceIte] using hh
  · intro hp
    have hh : ∀ i j, pairScore g psi A B i j=1 := by
      intro i j
      unfold pairScore
      split
      · exact hp i j (by assumption)
      · rfl
    change ∑ i, ∑ j, g.pi i j*pairScore g psi A B i j=1
    simp only [hh,mul_one]
    exact g.pi_normalized

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.positive_iff
#print axioms Blueprint.SpatialProof.tensor_adjoint_identity
#print axioms Blueprint.SpatialProof.tensor_expectation_nonneg
#print axioms Blueprint.SpatialProof.completion_add
#print axioms Blueprint.SpatialProof.completion_id
#print axioms Blueprint.SpatialProof.expect
#print axioms Blueprint.SpatialProof.expect_add_left
#print axioms Blueprint.SpatialProof.expect_add_right
#print axioms Blueprint.SpatialProof.expect_zero_left
#print axioms Blueprint.SpatialProof.expect_sum_left
#print axioms Blueprint.SpatialProof.expect_id
#print axioms Blueprint.SpatialProof.matching_probability_le_one
#print axioms Blueprint.SpatialProof.pairScore
#print axioms Blueprint.SpatialProof.pair_score_le_one
#print axioms Blueprint.SpatialProof.weighted_average_one
#print axioms Blueprint.SpatialProof.perfect_iff_pointwise
