import Companion.HilbertSchmidt
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp

namespace Companion.Analytic
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 400000

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem hsNorm_isometry_left [DecidableEq β] (V : Matrix α β ℂ)
    (A : Matrix β γ ℂ) (hV : V.conjTranspose*V=1) : hsNorm (V*A)=hsNorm A := by
  apply congrArg Real.sqrt
  rw [hsSquared_trace,hsSquared_trace]
  have he : (V*A).conjTranspose*(V*A)=A.conjTranspose*A := by
    rw [Matrix.conjTranspose_mul]
    calc
      A.conjTranspose*V.conjTranspose*(V*A)=A.conjTranspose*((V.conjTranspose*V)*A) := by
        simp only [Matrix.mul_assoc]
      _=A.conjTranspose*A := by rw [hV,Matrix.one_mul]
  rw [he]

def uniformCoefficient (β : Type*) [Fintype β] : ℝ := (Real.sqrt (Fintype.card β))⁻¹

theorem uniformCoefficient_square (β : Type*) [Fintype β] [Nonempty β] :
    uniformCoefficient β*uniformCoefficient β*(Fintype.card β:ℝ)=1 := by
  have hn : 0<(Fintype.card β:ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card β:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  unfold uniformCoefficient
  calc
    _=(Real.sqrt (Fintype.card β:ℝ))⁻¹*(Real.sqrt (Fintype.card β:ℝ))⁻¹*
        (Real.sqrt (Fintype.card β:ℝ))^2 := by rw [Real.sq_sqrt hn.le]
    _=1 := by field_simp

def uniformEmbedding [DecidableEq α] (F : β → Matrix.unitaryGroup α ℂ) : Matrix (β × α) α ℂ :=
  fun ba i => (uniformCoefficient β:ℂ)*(F ba.1:Matrix α α ℂ) ba.2 i

/-- The coherent uniform sum of any finite family of unitaries is an
isometry, regardless of any commutation relations among the family. -/
theorem uniformEmbedding_isometry [DecidableEq α] [Nonempty β]
    (F : β → Matrix.unitaryGroup α ℂ) :
    (uniformEmbedding F).conjTranspose*uniformEmbedding F=1 := by
  classical
  have hc : (uniformCoefficient β:ℂ)*(uniformCoefficient β:ℂ)*(Fintype.card β:ℂ)=1 := by
    exact_mod_cast uniformCoefficient_square β
  have he : (uniformEmbedding F).conjTranspose*uniformEmbedding F=
      ((uniformCoefficient β:ℂ)*(uniformCoefficient β:ℂ)) •
        ∑ b, (F b:Matrix α α ℂ).conjTranspose*(F b:Matrix α α ℂ) := by
    ext i j
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,uniformEmbedding,Fintype.sum_prod_type,
      Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
    ring
  rw [he]
  have hf (b : β) : (F b:Matrix α α ℂ).conjTranspose*(F b:Matrix α α ℂ)=1 := (F b).property.1
  simp_rw [hf]
  have hsum : (∑ _b : β, (1:Matrix α α ℂ))=(Fintype.card β:ℂ) • (1:Matrix α α ℂ) := by
    simp [Algebra.smul_def]
  rw [hsum,smul_smul,hc,one_smul]

theorem uniformEmbedding_hs [DecidableEq α] [Nonempty β]
    (F : β → Matrix.unitaryGroup α ℂ) (A : Matrix α γ ℂ) :
    hsNorm (uniformEmbedding F*A)=hsNorm A :=
  hsNorm_isometry_left _ _ (uniformEmbedding_isometry F)

def involutionUnitary {d : Nat} (Z : Mat d) (h : IsInvolution Z) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨Z,by
    change Z.conjTranspose*Z=1 ∧ Z*Z.conjTranspose=1
    constructor <;> rw [h.1,h.2]⟩

def orderedZUnitary {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (g : Fin M → Bool) : Matrix.unitaryGroup (Fin d) ℂ :=
  (List.ofFn (fun i => if g i then involutionUnitary (Z i) (hZ i) else 1)).prod

theorem orderedZUnitary_matrix {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (g : Fin M → Bool) : (orderedZUnitary Z hZ g:Mat d)=orderedZ Z g := by
  change (Matrix.unitaryGroup (Fin d) ℂ).subtype
      ((List.ofFn (fun i => if g i then involutionUnitary (Z i) (hZ i) else 1)).prod)=_
  rw [map_list_prod]
  simp only [List.map_ofFn,Function.comp_def,orderedZ]
  congr 2
  funext i
  split <;> rfl

def countEmbedding {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i)) :
    Matrix ((Fin M → Bool) × Fin d) (Fin d) ℂ := uniformEmbedding (orderedZUnitary Z hZ)

theorem countEmbedding_isometry {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i)) :
    (countEmbedding Z hZ).conjTranspose*countEmbedding Z hZ=1 :=
  uniformEmbedding_isometry _

theorem countEmbedding_apply {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (g : Fin M → Bool) (a b : Fin d) :
    countEmbedding Z hZ (g,a) b=(Real.sqrt ((2:ℝ)^M))⁻¹*(orderedZ Z g) a b := by
  simp only [countEmbedding,uniformEmbedding,uniformCoefficient,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,orderedZUnitary_matrix]

theorem countEmbedding_hs {M d : Nat} (Z : Fin M → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (A : Mat d) : hsNorm (countEmbedding Z hZ*A)=hsNorm A := uniformEmbedding_hs _ _

end
end Companion.Analytic
