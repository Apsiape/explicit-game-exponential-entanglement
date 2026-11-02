import Companion.ZeroDiagonal
import Companion.BinaryQuantumStates

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

variable {a b : Type*} [Fintype a] [Fintype b]

def factorVector (L : Matrix a b ℂ) : EuclideanSpace ℂ (a × b) :=
  WithLp.toLp 2 (fun ij => L ij.1 ij.2)

theorem factorVector_norm (L : Matrix a b ℂ) : ‖factorVector L‖=hsNorm L := by
  apply (sq_eq_sq₀ (norm_nonneg _) (hsNorm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,hsNorm_sq]
  simp only [factorVector,hsSquared,Fintype.sum_prod_type,Complex.normSq_eq_norm_sq]

theorem factorVector_sub (L L' : Matrix a b ℂ) : factorVector (L-L')=factorVector L-factorVector L' := rfl

theorem factorVector_inner (L L' : Matrix a b ℂ) :
    inner ℂ (factorVector L) (factorVector L')=Matrix.trace (L.conjTranspose*L') := by
  simp only [factorVector,PiLp.inner_apply,RCLike.inner_apply,Fintype.sum_prod_type,
    Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,mul_comm]
  exact Finset.sum_comm

theorem factor_overlap_bound (L L' : Matrix a b ℂ) :
    ‖Matrix.trace (L.conjTranspose*L')‖≤hsNorm L*hsNorm L' := by
  rw [← factorVector_inner,← factorVector_norm,← factorVector_norm]
  exact norm_inner_le_norm _ _

theorem factor_distance_sq (L L' : Matrix a b ℂ) :
    hsNorm (L-L')^2=hsNorm L^2-2*(Matrix.trace (L.conjTranspose*L')).re+hsNorm L'^2 := by
  have h := norm_sub_sq (𝕜:=ℂ) (factorVector L) (factorVector L')
  simp only [← factorVector_sub,factorVector_norm,factorVector_inner] at h
  change hsNorm (L-L')^2=hsNorm L^2-2*(Matrix.trace (L.conjTranspose*L')).re+hsNorm L'^2 at h
  exact h

theorem factor_hs_smul (c : ℂ) (L : Matrix a b ℂ) : hsNorm (c • L)=‖c‖*hsNorm L := by
  simp only [hsNorm_eq_frobenius,norm_smul]

def alignmentPhase (z : ℂ) : ℂ := if z=0 then 1 else star z/(‖z‖:ℂ)

theorem alignmentPhase_norm (z : ℂ) : ‖alignmentPhase z‖=1 := by
  by_cases hz : z=0
  · simp [alignmentPhase,hz]
  · simp [alignmentPhase,hz,norm_div,norm_star,Complex.norm_real,abs_of_nonneg (norm_nonneg z),
      norm_ne_zero_iff.mpr hz]

theorem alignmentPhase_mul (z : ℂ) : alignmentPhase z*z=(‖z‖:ℂ) := by
  by_cases hz : z=0
  · simp [alignmentPhase,hz]
  · have hn : (‖z‖:ℂ)≠0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    have hs : star z*z=((‖z‖^2:ℝ):ℂ) := by
      rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    rw [alignmentPhase,if_neg hz]
    calc
      _=(star z*z)/(‖z‖:ℂ) := by ring
      _=(‖z‖:ℂ) := by rw [hs,Complex.ofReal_pow]; field_simp

theorem aligned_overlap (L L' : Matrix a b ℂ) :
    Matrix.trace (L.conjTranspose*(alignmentPhase (Matrix.trace (L.conjTranspose*L')) • L'))=
      (‖Matrix.trace (L.conjTranspose*L')‖:ℂ) := by
  rw [Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,alignmentPhase_mul]

theorem aligned_factor_product (L L' : Matrix a b ℂ) :
    (alignmentPhase (Matrix.trace (L.conjTranspose*L')) • L')*
        (alignmentPhase (Matrix.trace (L.conjTranspose*L')) • L').conjTranspose=L'*L'.conjTranspose := by
  let c := alignmentPhase (Matrix.trace (L.conjTranspose*L'))
  have hc : c*star c=1 := by
    rw [mul_comm,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    simp [c,alignmentPhase_norm]
  change (c • L')*(c • L').conjTranspose=_
  rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc,one_smul]

def factorState [DecidableEq a] (L : Matrix a b ℂ) (hn : hsNorm L=1) : QIT.State a where
  matrix := L*L.conjTranspose
  pos := Matrix.posSemidef_self_mul_conjTranspose L
  trace_eq_one := by
    rw [Matrix.trace_mul_comm,gram_trace]
    have h : hsSquared L=1 := by rw [← hsNorm_sq,hn]; norm_num
    rw [h,Complex.ofReal_one]

end
end Companion.Analytic.CountProof
