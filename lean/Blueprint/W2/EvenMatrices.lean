import Blueprint.W2.EvenPhase
import Blueprint.W2.KNormalized

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def evenClock (m : Nat) : Mat (2*m) := Matrix.diagonal (fun i => evenPhase m i.val)

theorem evenClock_unitary (m : Nat) : IsUnitary (evenClock m) := by
  constructor <;> simp only [evenClock,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Pi.star_apply]
  · have he : (fun i : Fin (2*m) => star (evenPhase m i.val)*evenPhase m i.val)=fun _ => (1:ℂ) := by
      funext i
      exact (evenPhase_unit m i.val).1
    rw [he,Matrix.diagonal_one]
  · have he : (fun i : Fin (2*m) => evenPhase m i.val*star (evenPhase m i.val))=fun _ => (1:ℂ) := by
      funext i
      exact (evenPhase_unit m i.val).2
    rw [he,Matrix.diagonal_one]

theorem halfSwap_matrix_square (m : Nat) (hm : 0<m) :
    (halfSwap m hm).permMatrix ℂ*(halfSwap m hm).permMatrix ℂ=1 := by
  rw [←Matrix.permMatrix_mul,halfSwap_square,Matrix.permMatrix_one]

theorem clock_half_conjugation (m : Nat) (hm : 0<m) :
    (halfSwap m hm).permMatrix ℂ*evenClock m*((halfSwap m hm).permMatrix ℂ).conjTranspose= -evenClock m := by
  rw [evenClock,perm_diagonal_conjugation]
  simp_rw [evenPhase_shift]
  simp [Matrix.diagonal_neg]

theorem flipped_conjugation {d : Nat} (P Y : Mat d) (hP : IsUnitary P) (hY : IsUnitary Y)
    (hflip : P*Y*P.conjTranspose= -Y) : Y*P*Y.conjTranspose= -P := by
  have he : P*Y= -Y*P := by
    have h := congrArg (fun M : Mat d => M*P) hflip
    simpa only [Matrix.mul_assoc,hP.1,Matrix.mul_one] using h
  have he' : Y*P= -(P*Y) := by rw [he]; simp
  rw [he',Matrix.neg_mul,Matrix.mul_assoc,hY.2,Matrix.mul_one]

theorem clock_shuffle_residual (m : Nat) (hm : 0<m) :
    (shuffle m hm).permMatrix ℂ*evenClock m*((shuffle m hm).permMatrix ℂ).conjTranspose*
      (evenClock m).conjTranspose*(evenClock m).conjTranspose-1=
        Matrix.diagonal (fun i : Fin (2*m) => if i.val<m then 0 else evenPhase m 1-1) := by
  rw [evenClock,perm_diagonal_conjugation]
  simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Pi.star_apply]
  rw [←Matrix.diagonal_one,Matrix.diagonal_sub]
  apply congrArg Matrix.diagonal
  funext i
  rw [evenPhase_shuffle]
  by_cases hi : i.val<m
  · simp only [hi,↓reduceIte,mul_one]
    have hunit := (evenPhase_unit m i.val).2
    calc
      _=(evenPhase m i.val*star (evenPhase m i.val))*(evenPhase m i.val*star (evenPhase m i.val))-1 := by ring
      _=0 := by rw [hunit]; ring
  · simp only [hi,↓reduceIte]
    have hunit := (evenPhase_unit m i.val).2
    calc
      _=(evenPhase m i.val*star (evenPhase m i.val))*(evenPhase m i.val*star (evenPhase m i.val))*evenPhase m 1-1 := by ring
      _=_ := by rw [hunit]; ring

theorem hsSquared_diagonal {d : Nat} (v : Fin d → ℂ) :
    hsSquared (Matrix.diagonal v)=∑ i, Complex.normSq (v i) := by
  simp [hsSquared,Matrix.diagonal_apply,apply_ite]

theorem upper_half_sum (m : Nat) (c : ℝ) :
    (∑ i : Fin (2*m), if i.val<m then (0:ℝ) else c)=(m:ℝ)*c := by
  have he : 2*m=m+m := by omega
  rw [he,Fin.sum_univ_add]
  have hleft (i : Fin m) : (i.castAdd m).val<m := i.isLt
  have hright (i : Fin m) : ¬(i.natAdd m).val<m := by simp
  simp [hleft,hright]

theorem evenPhase_defect_square (m : Nat) (hm : 0<m) :
    Complex.normSq (evenPhase m 1-1)=4*Real.sin (Real.pi/(2*m))^2 := by
  rw [Complex.normSq_eq_norm_sq,evenPhase]
  simp only [Nat.cast_one,mul_one]
  rw [mul_comm _ Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,sq_abs,mul_pow]
  have he : (Real.pi/(m:ℝ))/2=Real.pi/(2*m) := by ring
  rw [he]
  norm_num

theorem even_residual_norm (m : Nat) (hm : 0<m) :
    normalizedHS (Matrix.diagonal (fun i : Fin (2*m) => if i.val<m then 0 else evenPhase m 1-1))=
      Real.sqrt 2*Real.sin (Real.pi/(2*m)) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hden : (0:ℝ)<(2*m:Nat) := by positivity
  have hsin : 0≤Real.sin (Real.pi/(2*m)) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    ((div_le_iff₀ (by positivity : (0:ℝ)<2*m)).mpr (by
      have hM : (1:ℝ)≤m := by exact_mod_cast hm
      nlinarith [Real.pi_pos]))
  apply (sq_eq_sq₀ (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (hsNorm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) hsin)).mp
  have hsum : hsSquared (Matrix.diagonal (fun i : Fin (2*m) => if i.val<m then 0 else evenPhase m 1-1))=
      (m:ℝ)*(4*Real.sin (Real.pi/(2*m))^2) := by
    rw [hsSquared_diagonal]
    simp only [apply_ite,Complex.normSq_zero,evenPhase_defect_square m hm]
    exact upper_half_sum m _
  change ((Real.sqrt (2*m:Nat))⁻¹*hsNorm _)^2=_
  rw [mul_pow,inv_pow,Real.sq_sqrt hden.le,hsNorm_sq,hsum,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  push_cast
  field_simp
  ring

end
end Blueprint.W2
