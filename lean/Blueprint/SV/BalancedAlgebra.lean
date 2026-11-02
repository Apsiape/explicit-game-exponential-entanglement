import Blueprint.SV.PermutationReflection
import Companion.ScalarPhase
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace Blueprint.SV
noncomputable section
open Companion Companion.Analytic Companion.DoubleMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

def permutationUnitary (p : Equiv.Perm α) : U α :=
  ⟨p.permMatrix ℂ,by
    change (p.permMatrix ℂ).conjTranspose * p.permMatrix ℂ = 1 ∧
      p.permMatrix ℂ * (p.permMatrix ℂ).conjTranspose = 1
    constructor <;> rw [Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul] <;> simp⟩

theorem permutationUnitary_square (p : Equiv.Perm α) (h : p*p=1) :
    permutationUnitary p * permutationUnitary p = 1 := by
  apply Subtype.ext
  change p.permMatrix ℂ * p.permMatrix ℂ = 1
  rw [←Matrix.permMatrix_mul,h,Matrix.permMatrix_one]

/-- The cycle reflections used in Lemma 11.13 give an involution reversing X. -/
theorem permutationUnitary_reverses (p : Equiv.Perm α) :
    permutationUnitary (reversingPermutation p) * permutationUnitary p *
      permutationUnitary (reversingPermutation p) = (permutationUnitary p)⁻¹ := by
  apply Subtype.ext
  change (reversingPermutation p).permMatrix ℂ * p.permMatrix ℂ *
    (reversingPermutation p).permMatrix ℂ = (p.permMatrix ℂ).conjTranspose
  rw [Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul,←Matrix.permMatrix_mul]
  rw [←mul_assoc,reversingPermutation_conjugates]

theorem permutation_involutive_factorization (p : Equiv.Perm α) :
    ∃ F V : U α, F*F=1 ∧ V*V=1 ∧ F*V=permutationUnitary p := by
  let T := permutationUnitary (reversingPermutation p)
  let X := permutationUnitary p
  have hT : T*T=1 := permutationUnitary_square _ (reversingPermutation_square p)
  have hrev : T*X*T=X⁻¹ := permutationUnitary_reverses p
  refine ⟨T,T*X,hT,?_,?_⟩
  · calc
      (T*X)*(T*X) = (T*X*T)*X := by group
      _ = 1 := by rw [hrev,inv_mul_cancel]
  · change T*(T*X)=X
    rw [←mul_assoc,hT,one_mul]

/-- Eliminating x with these factors does not add any matrix blocks. -/
theorem doubled_involutive_factorization (p : Equiv.Perm α) :
    ∃ F V : U (Bool × α), F*F=1 ∧ V*V=1 ∧
      F*V=diag (permutationUnitary p) (permutationUnitary p) := by
  obtain ⟨F,V,hF,hV,hX⟩ := permutation_involutive_factorization p
  refine ⟨diag F F,diag V V,?_,?_,?_⟩
  · simpa [mono_mul,hF] using (mono_one (α:=α))
  · simpa [mono_mul,hV] using (mono_one (α:=α))
  · simp only [mono_mul,Bool.false_eq_true,↓reduceIte,Bool.xor_false,hX]

theorem conjugate_square {G : Type*} [Group G] (V S : G)
    (hV : V*V=1) (hS : S*S=1) : (V*S*V)*(V*S*V)=1 := by
  calc
    _ = V*S*(V*V)*S*V := by group
    _ = V*(S*S)*V := by rw [hV]; group
    _ = 1 := by rw [hS,mul_one,hV]

/-- Both defining conjugacies have exactly the old residual after splitting X. -/
theorem split_conjugacy_residual {G : Type*} [Group G] (F V S T : G)
    (hF : F*F=1) (hV : V*V=1) :
    F*(V*S*V)*F*T⁻¹ = (F*V)*S*(F*V)⁻¹*T⁻¹ := by
  have hiF : F⁻¹=F := inv_eq_of_mul_eq_one_left hF
  have hiV : V⁻¹=V := inv_eq_of_mul_eq_one_left hV
  simp only [mul_inv_rev,hiF,hiV,mul_assoc]

def liftedY (Y : U α) : U (Bool × α) := anti Y⁻¹ Y
def firstLiftAncilla (Y S : U α) : U (Bool × α) := liftedY Y * diag S 1 * liftedY Y
def firstLiftPower (Y : U α) : U (Bool × α) := liftedY Y * swap α * liftedY Y

theorem liftedY_square (Y : U α) : liftedY Y * liftedY Y = 1 := by
  simp [liftedY,mono_mul,mono_one]

theorem firstLift_product (Y : U α) : swap α * liftedY Y = diag Y Y⁻¹ := by
  simp [swap,liftedY,mono_mul]

theorem firstLiftAncilla_formula (Y S : U α) : firstLiftAncilla Y S = diag 1 (Y*S*Y⁻¹) := by
  simp [firstLiftAncilla,liftedY,mono_mul,mul_assoc]

theorem firstLift_conjugacy_residual (Y A B : U α) :
    swap α * firstLiftAncilla Y A * swap α * (diag B 1)⁻¹ =
      diag (Y*A*Y⁻¹*B⁻¹) 1 := by
  simp [firstLiftAncilla_formula,swap,mono_mul,mono_inv,mul_assoc]

theorem firstLiftPower_formula (Y : U α) : firstLiftPower Y = anti (Y⁻¹*Y⁻¹) (Y*Y) := by
  simp [firstLiftPower,liftedY,swap,mono_mul]

theorem firstLiftPower_square (Y : U α) : firstLiftPower Y * firstLiftPower Y = 1 :=
  conjugate_square _ _ (liftedY_square Y) ScalarPhase.swap_square

def powerResidual (X Y : U α) : U α := X*Y*X⁻¹*(Y*Y)⁻¹

theorem firstLift_power_residual (X Y : U α) :
    diag X X * liftedY Y * (diag X X)⁻¹ * (firstLiftPower Y)⁻¹ =
      diag ((Y*Y)⁻¹*(powerResidual X Y)⁻¹*(Y*Y)) (powerResidual X Y) := by
  simp only [liftedY,firstLiftPower_formula,mono_mul,mono_inv]
  dsimp
  congr 1 <;> dsimp [powerResidual] <;> group
  all_goals simp only [zpow_ofNat,pow_two,mul_assoc]

/-- The only inexact relation keeps its defect through the first lift. -/
theorem firstLift_power_bound (hc : 0<Fintype.card α) (X Y : U α) (e : ℝ)
    (he : 0≤e) (hr : defect (powerResidual X Y)≤e) :
    defect (diag X X * liftedY Y * (diag X X)⁻¹ * (firstLiftPower Y)⁻¹) ≤ e := by
  rw [firstLift_power_residual]
  apply diagonal_bound hc _ _ e he _ hr
  have h : defect ((Y*Y)⁻¹*(powerResidual X Y)⁻¹*(Y*Y)) = defect (powerResidual X Y) := by
    calc
      _ = defect ((powerResidual X Y)⁻¹) := by
        simpa only [DoubleMatrix.length,inv_inv] using
          (DoubleMatrix.length (α:=α)).conjugate ((Y*Y)⁻¹) ((powerResidual X Y)⁻¹)
      _ = defect (powerResidual X Y) := by
        simpa only [DoubleMatrix.length] using (DoubleMatrix.length (α:=α)).inv (powerResidual X Y)
  rwa [h]

/-- The marked involution stays balanced, and the commutator extension is exact. -/
theorem balanced_marker :
    let C : U (Bool × α) := diag (ScalarPhase.minusOne α) 1
    let T : U (Bool × α) := swap α
    let W : U (Bool × α) := diag 1 (ScalarPhase.minusOne α)
    C*C=1 ∧ T*T=1 ∧ W*W=1 ∧ T*C*T=W ∧ C*W=ScalarPhase.minusOne (Bool × α) := by
  dsimp
  refine ⟨?_,ScalarPhase.swap_square,ScalarPhase.u_square,ScalarPhase.switch,ScalarPhase.diagonal_product⟩
  simpa [mono_mul,ScalarPhase.square] using (mono_one (α:=α))

end
end Blueprint.SV

#print axioms Blueprint.SV.permutationUnitary
#print axioms Blueprint.SV.permutationUnitary_square
#print axioms Blueprint.SV.permutationUnitary_reverses
#print axioms Blueprint.SV.permutation_involutive_factorization
#print axioms Blueprint.SV.doubled_involutive_factorization
#print axioms Blueprint.SV.conjugate_square
#print axioms Blueprint.SV.split_conjugacy_residual
#print axioms Blueprint.SV.liftedY
#print axioms Blueprint.SV.firstLiftAncilla
#print axioms Blueprint.SV.firstLiftPower
#print axioms Blueprint.SV.liftedY_square
#print axioms Blueprint.SV.firstLift_product
#print axioms Blueprint.SV.firstLiftAncilla_formula
#print axioms Blueprint.SV.firstLift_conjugacy_residual
#print axioms Blueprint.SV.firstLiftPower_formula
#print axioms Blueprint.SV.firstLiftPower_square
#print axioms Blueprint.SV.powerResidual
#print axioms Blueprint.SV.firstLift_power_residual
#print axioms Blueprint.SV.firstLift_power_bound
#print axioms Blueprint.SV.balanced_marker
