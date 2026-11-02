import Companion.FactorGeometry

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 600000

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem factor_gram_one (L : Matrix a b ℂ) (hn : hsNorm L=1) : Matrix.trace (L.conjTranspose*L)=1 := by
  rw [gram_trace]
  have h : hsSquared L=1 := by rw [← hsNorm_sq,hn]; norm_num
  rw [h,Complex.ofReal_one]

theorem trace_cross_star (L B : Matrix a b ℂ) :
    Matrix.trace (B.conjTranspose*L)=star (Matrix.trace (L.conjTranspose*B)) := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

def pairBranch (L B : Matrix a b ℂ) (s : Bool) : Matrix a b ℂ := if s then L-B else L+B
def pairScale (p : ℝ) (s : Bool) : ℂ := (2*(Real.sqrt (binaryProbability p s):ℂ))⁻¹
def pairKraus (L B : Matrix a b ℂ) (p : ℝ) (k : b) : Matrix a Bool ℂ :=
  fun y s => pairScale p s*pairBranch L B s y k

theorem pairScale_star (p : ℝ) (s : Bool) : star (pairScale p s)=pairScale p s := by
  simp [pairScale,Complex.star_def]

theorem sum_cross_trace (L B : Matrix a b ℂ) :
    (∑ k, ∑ y, star (L y k)*B y k)=Matrix.trace (L.conjTranspose*B) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]

theorem pairKraus_gram (L B : Matrix a b ℂ) (p : ℝ) (u v : Bool) :
    (∑ k, (pairKraus L B p k).conjTranspose*pairKraus L B p k) u v=
      pairScale p u*pairScale p v*Matrix.trace ((pairBranch L B u).conjTranspose*pairBranch L B v) := by
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  have ht (k : b) (y : a) : star (pairKraus L B p k y u)*pairKraus L B p k y v=
      (pairScale p u*pairScale p v)*(star (pairBranch L B u y k)*pairBranch L B v y k) := by
    simp only [pairKraus,star_mul,pairScale_star]
    ring
  simp_rw [ht,← Finset.mul_sum]
  rw [sum_cross_trace]

theorem pairBranch_trace (L B : Matrix a b ℂ) (p : ℝ) (hL : hsNorm L=1) (hB : hsNorm B=1)
    (hc : Matrix.trace (L.conjTranspose*B)=((2*p-1:ℝ):ℂ)) (u v : Bool) :
    Matrix.trace ((pairBranch L B u).conjTranspose*pairBranch L B v)=
      if u=v then ((4*binaryProbability p u:ℝ):ℂ) else 0 := by
  have hLL := factor_gram_one L hL
  have hBB := factor_gram_one B hB
  have hBL : Matrix.trace (B.conjTranspose*L)=((2*p-1:ℝ):ℂ) := by
    rw [trace_cross_star,hc]
    simp
  cases u <;> cases v <;>
    simp [pairBranch,binaryProbability,Matrix.conjTranspose_add,Matrix.conjTranspose_sub,
      Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul,Matrix.trace_add,Matrix.trace_sub,
      hLL,hBB,hc,hBL] <;> push_cast <;> ring

theorem rootScale_square (x : ℝ) (hx : 0<x) :
    (2*(Real.sqrt x:ℂ))⁻¹*(2*(Real.sqrt x:ℂ))⁻¹*(4*(x:ℂ))=1 := by
  have hs : (Real.sqrt x:ℂ)^2=(x:ℂ) := by exact_mod_cast Real.sq_sqrt hx.le
  have hn : (2*(Real.sqrt x:ℂ))≠0 := mul_ne_zero (by norm_num)
    (by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hx)))
  calc
    _=(2*(Real.sqrt x:ℂ))⁻¹*(2*(Real.sqrt x:ℂ))⁻¹*(2*(Real.sqrt x:ℂ))^2 := by
      rw [mul_pow,hs]; norm_num
    _=1 := by field_simp

theorem pairKraus_complete (L B : Matrix a b ℂ) (p : ℝ) (hp0 : 0<p) (hp1 : p<1)
    (hL : hsNorm L=1) (hB : hsNorm B=1)
    (hc : Matrix.trace (L.conjTranspose*B)=((2*p-1:ℝ):ℂ)) :
    (∑ k, (pairKraus L B p k).conjTranspose*pairKraus L B p k)=1 := by
  ext u v
  rw [pairKraus_gram,pairBranch_trace L B p hL hB hc]
  by_cases huv : u=v
  · subst v
    simp only [ite_true,Matrix.one_apply_eq]
    have hx : 0<binaryProbability p u := by cases u <;> simp [binaryProbability] <;> linarith
    simpa only [pairScale,Complex.ofReal_mul,Complex.ofReal_ofNat] using rootScale_square (binaryProbability p u) hx
  · simp [huv,Matrix.one_apply]

theorem pairKraus_mulVec (L B : Matrix a b ℂ) (p : ℝ) (hp0 : 0<p) (hp1 : p<1)
    (k : b) (neg : Bool) :
    (pairKraus L B p k).mulVec (binaryAmplitude p neg)=fun y => (if neg then B else L) y k := by
  have ha : (Real.sqrt p:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp0))
  have hb : (Real.sqrt (1-p):ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hp1)))
  funext y
  cases neg <;>
    simp [Matrix.mulVec,dotProduct,Fintype.sum_bool,pairKraus,pairScale,pairBranch,binaryProbability,binaryAmplitude] <;>
    field_simp <;> ring

theorem pairKraus_image (L B : Matrix a b ℂ) (p : ℝ) (hp0 : 0<p) (hp1 : p<1) (neg : Bool) :
    QIT.MatrixMap.ofKraus (pairKraus L B p) (binaryPure p hp0.le hp1.le neg).state.matrix=
      (if neg then B else L)*(if neg then B else L).conjTranspose := by
  change (∑ k, pairKraus L B p k*QIT.rankOneMatrix (binaryAmplitude p neg)*
    (pairKraus L B p k).conjTranspose)=_
  simp_rw [← QIT.rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,pairKraus_mulVec L B p hp0 hp1]
  ext y z
  simp only [Matrix.sum_apply,QIT.rankOneMatrix_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]

def pairChannel (L B : Matrix a b ℂ) (p : ℝ) (hp0 : 0<p) (hp1 : p<1)
    (hL : hsNorm L=1) (hB : hsNorm B=1)
    (hc : Matrix.trace (L.conjTranspose*B)=((2*p-1:ℝ):ℂ)) : QIT.Channel Bool a :=
  krausChannel (pairKraus L B p) (pairKraus_complete L B p hp0 hp1 hL hB hc)

end
end Companion.Analytic.CountProof
