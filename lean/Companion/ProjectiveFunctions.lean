import Companion.GameLossBounds

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

variable {y a : Type*} [Fintype y] [DecidableEq y] [Fintype a] [DecidableEq a]

def pvmFunction (P : QIT.ProjectiveMeasurement y a) (f : y → ℂ) : Matrix a a ℂ :=
  ∑ u, f u • P.effects u

theorem pvmFunction_one (P : QIT.ProjectiveMeasurement y a) : pvmFunction P (fun _ => 1)=1 := by
  simpa only [pvmFunction,one_smul] using P.sum_eq_one

theorem pvmFunction_constant (P : QIT.ProjectiveMeasurement y a) (c : ℂ) :
    pvmFunction P (fun _ => c)=c • 1 := by
  rw [pvmFunction,← Finset.smul_sum,P.sum_eq_one]

theorem pvmFunction_mul_projection (P : QIT.ProjectiveMeasurement y a) (f : y → ℂ) (u : y) :
    pvmFunction P f*P.effects u=f u • P.effects u := by
  rw [pvmFunction,Matrix.sum_mul]
  calc
    _=∑ v, if v=u then f u • P.effects u else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Matrix.smul_mul,projective_effect_mul]
      by_cases h : v=u
      · subst v; simp
      · simp [h]
    _=_ := by simp

theorem pvmFunction_mul (P : QIT.ProjectiveMeasurement y a) (f g : y → ℂ) :
    pvmFunction P f*pvmFunction P g=pvmFunction P (fun u => f u*g u) := by
  change pvmFunction P f*(∑ u, g u • P.effects u)=_
  rw [Matrix.mul_sum]
  simp_rw [Matrix.mul_smul,pvmFunction_mul_projection,smul_smul,mul_comm]
  rfl

theorem pvmFunction_commute (P : QIT.ProjectiveMeasurement y a) (f g : y → ℂ) :
    Commute (pvmFunction P f) (pvmFunction P g) := by
  change pvmFunction P f*pvmFunction P g=pvmFunction P g*pvmFunction P f
  rw [pvmFunction_mul,pvmFunction_mul]
  simp only [mul_comm]

theorem pvmFunction_conjTranspose (P : QIT.ProjectiveMeasurement y a) (f : y → ℂ) :
    (pvmFunction P f).conjTranspose=pvmFunction P (fun u => star (f u)) := by
  have hh : ∀ u, (P.effects u).conjTranspose=P.effects u := fun u => (P.isHermitian u).eq
  simp only [pvmFunction,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,hh]

theorem pvmFunction_product (P : QIT.ProjectiveMeasurement y a) (L : List (y → ℂ)) :
    (L.map (pvmFunction P)).prod=pvmFunction P (fun u => (L.map (fun f => f u)).prod) := by
  induction L with
  | nil => simp only [List.map_nil,List.prod_nil,pvmFunction_one]
  | cons f L ih =>
    simp only [List.map_cons,List.prod_cons,ih,pvmFunction_mul]

def transposePVM (P : QIT.ProjectiveMeasurement y a) : QIT.ProjectiveMeasurement y a where
  effects u := (P.effects u).transpose
  isHermitian u := (P.isHermitian u).transpose
  idempotent u := by rw [← Matrix.transpose_mul,P.idempotent u]
  orthogonal u v huv := by rw [← Matrix.transpose_mul,P.orthogonal v u (Ne.symm huv)]; rfl
  sum_eq_one := by
    have ht : (∑ u, (P.effects u).transpose)=(∑ u, P.effects u).transpose := by
      ext i j; simp only [Matrix.sum_apply,Matrix.transpose_apply]
    rw [ht,P.sum_eq_one,Matrix.transpose_one]

theorem pvmFunction_transpose (P : QIT.ProjectiveMeasurement y a) (f : y → ℂ) :
    (pvmFunction P f).transpose=pvmFunction (transposePVM P) f := by
  ext i j
  simp only [pvmFunction,Matrix.transpose_apply,Matrix.sum_apply,Matrix.smul_apply,transposePVM]

end
end Companion.Analytic.TransferProof
