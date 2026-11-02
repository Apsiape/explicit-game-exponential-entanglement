import Blueprint.RatesDefinitions
import Blueprint.W2.CHSHPair

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 600000

theorem hs_identity (d : Nat) : hsNorm (1:Mat d)^2=d := by
  rw [hsNorm_sq]
  simp [hsSquared,Matrix.one_apply]

theorem normalized_minus_identity (d : Nat) (hd : 0<d) : normalizedHS (-1-1:Mat d)=2 := by
  have hs : 0<Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hI : hsNorm (1:Mat d)=Real.sqrt (d:ℝ) := by
    apply (sq_eq_sq₀ (hsNorm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hs_identity,Real.sq_sqrt (Nat.cast_nonneg _)]
  have he : (-1-1:Mat d)=(-2:ℂ) • (1:Mat d) := by module
  rw [he,normalizedHS,hsNorm_eq_frobenius,norm_smul,←hsNorm_eq_frobenius,hI]
  norm_num
  field_simp

theorem maximal_unitary_separation {d : Nat} (hd : 0<d) (U : Mat d) (hU : IsUnitary U)
    (hsep : 2≤normalizedHS (U-1)) : U=-1 := by
  have hs : 0<Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hI := hs_identity d
  have hUN : hsNorm U^2=d := by rw [hsNorm_sq,hsSquared_trace,hU.1]; simp [Matrix.trace]
  have hminus := rectangular_sub_square U (1:Mat d)
  have hplus := rectangular_sub_square U (-1:Mat d)
  simp only [hs_eq_hsNorm,Matrix.conjTranspose_neg,Matrix.conjTranspose_one,
    Matrix.mul_neg,Matrix.mul_one,Matrix.trace_neg,Complex.neg_re,sub_neg_eq_add,
    hsNorm_eq_frobenius,norm_neg] at hminus hplus
  simp only [normalizedHS] at hsep
  have hmul : 2*Real.sqrt (d:ℝ)≤hsNorm (U-1) := by
    have h := mul_le_mul_of_nonneg_left hsep hs.le
    simpa only [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hs),one_mul,mul_comm] using h
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*Real.sqrt (d:ℝ)) hmul 2
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  have hz : hsNorm (U+1)=0 := by
    simp only [hsNorm_eq_frobenius] at hI hUN hsq ⊢
    nlinarith [norm_nonneg (U+1)]
  have he : U+1=0 := by simpa only [hsNorm_eq_frobenius,norm_eq_zero] using hz
  exact eq_neg_of_add_eq_zero_left he

theorem flat_kModel {d : Nat} (hd : 0<d) (U : Nat → Mat d) (e : ℝ) (he : 0≤e)
    (hr : normalizedRepresentation kRelators U e) (hJ : U 3=-1) :
    kModel U (MainProof.flatState d hd) e := by
  refine ⟨hr.1,?_,?_,?_⟩
  · intro r hmem
    rw [MainProof.flatState_weighted_norm]
    exact hr.2 r hmem
  · intro j _ _
    rw [MainProof.flatState_commutes]
    simpa [hs] using he
  · rw [hJ,neg_add_cancel,Matrix.zero_mul]
    simpa [hs] using he

theorem kHyperlinearProfile_mono_delta (delta : ℝ) (hdelta : delta≤2) (e : ℝ) :
    kHyperlinearProfile delta e≤kHyperlinearProfile 2 e := by
  unfold kHyperlinearProfile
  apply le_sInf
  rintro v ⟨d,U,hd,hr,hsep,rfl⟩
  exact sInf_le ⟨d,U,hd,hr,hdelta.trans hsep,rfl⟩

end
end Blueprint.W2
