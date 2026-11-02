import Blueprint.FNormal

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem diagonal_overlap {d : Nat} (U V W : Mat d) (z w : Fin d → ℂ)
    (hV : IsUnitary V) (hW : IsUnitary W)
    (hz : U=V*Matrix.diagonal z*V.conjTranspose)
    (hw : U=W*Matrix.diagonal w*W.conjTranspose) :
    Matrix.diagonal z*(V.conjTranspose*W)=(V.conjTranspose*W)*Matrix.diagonal w := by
  have hleft : V.conjTranspose*U=Matrix.diagonal z*V.conjTranspose := by
    rw [hz]
    calc
      _=(V.conjTranspose*V)*Matrix.diagonal z*V.conjTranspose := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hV.1,Matrix.one_mul]
  have hright : U*W=W*Matrix.diagonal w := by
    rw [hw]
    calc
      _=W*Matrix.diagonal w*(W.conjTranspose*W) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hW.1,Matrix.mul_one]
  calc
    _=(Matrix.diagonal z*V.conjTranspose)*W := by rw [Matrix.mul_assoc]
    _=(V.conjTranspose*U)*W := by rw [hleft]
    _=V.conjTranspose*(U*W) := Matrix.mul_assoc _ _ _
    _=V.conjTranspose*(W*Matrix.diagonal w) := by rw [hright]
    _=_ := (Matrix.mul_assoc _ _ _).symm

theorem diagonal_function_intertwine {d : Nat} (H : Mat d) (z w : Fin d → ℂ)
    (h : Matrix.diagonal z*H=H*Matrix.diagonal w) (f : ℂ → ℂ) :
    Matrix.diagonal (fun i => f (z i))*H=H*Matrix.diagonal (fun i => f (w i)) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at hij ⊢
  by_cases heq : z i=w j
  · rw [heq,mul_comm]
  · have hzero : H i j=0 := by
      apply (mul_eq_zero.mp (show (z i-w j)*H i j=0 by linear_combination hij)).resolve_left
      exact sub_ne_zero.mpr heq
    simp [hzero]

theorem functional_resolution {d : Nat} (U V W : Mat d) (z w : Fin d → ℂ)
    (hV : IsUnitary V) (hW : IsUnitary W)
    (hz : U=V*Matrix.diagonal z*V.conjTranspose)
    (hw : U=W*Matrix.diagonal w*W.conjTranspose) (f : ℂ → ℂ) :
    V*Matrix.diagonal (fun i => f (z i))*V.conjTranspose=
      W*Matrix.diagonal (fun i => f (w i))*W.conjTranspose := by
  have h := diagonal_function_intertwine (V.conjTranspose*W) z w
    (diagonal_overlap U V W z w hV hW hz hw) f
  have hcancel (B : Mat d) : B*W*W.conjTranspose=B := by
    rw [Matrix.mul_assoc,hW.2,Matrix.mul_one]
  have hunit : V*(V.conjTranspose*W)=W := by
    rw [←Matrix.mul_assoc,hV.2,Matrix.one_mul]
  calc
    _=V*(Matrix.diagonal (fun i => f (z i))*(V.conjTranspose*W))*W.conjTranspose := by
      simpa only [Matrix.mul_assoc] using (hcancel (V*Matrix.diagonal (fun i => f (z i))*V.conjTranspose)).symm
    _=V*((V.conjTranspose*W)*Matrix.diagonal (fun i => f (w i)))*W.conjTranspose := by rw [h]
    _=_ := by rw [←Matrix.mul_assoc V (V.conjTranspose*W),hunit]

theorem weighted_trace {d : Nat} (V rho : Mat d) (f : Fin d → ℂ) :
    (rho*(V*Matrix.diagonal f*V.conjTranspose)).trace=
      ∑ i, (V.conjTranspose*rho*V) i i*f i := by
  have ht := Matrix.trace_mul_cycle V.conjTranspose rho (V*Matrix.diagonal f)
  calc
    _=(V*Matrix.diagonal f*V.conjTranspose*rho).trace := Matrix.trace_mul_comm _ _
    _=(V.conjTranspose*rho*V*Matrix.diagonal f).trace := by
      simpa only [Matrix.mul_assoc] using ht.symm
    _=_ := by simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal]

theorem spectral_weighted_sum {d : Nat} (U V W rho : Mat d) (z w : Fin d → ℂ)
    (hV : IsUnitary V) (hW : IsUnitary W)
    (hz : U=V*Matrix.diagonal z*V.conjTranspose)
    (hw : U=W*Matrix.diagonal w*W.conjTranspose) (f : ℂ → ℂ) :
    (∑ i, (V.conjTranspose*rho*V) i i*f (z i))=
      ∑ i, (W.conjTranspose*rho*W) i i*f (w i) := by
  rw [←weighted_trace,←weighted_trace,functional_resolution U V W z w hV hW hz hw f]

theorem state_factor_rows {d : Nat} (V W : Mat d) (hW : IsUnitary W) (s : State d) :
    (V.conjTranspose*s.xi*W)*(V.conjTranspose*s.xi*W).conjTranspose=
      V.conjTranspose*s.rho*V := by
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,s.xi_positive.isHermitian.eq]
  calc
    _=V.conjTranspose*s.xi*(W*W.conjTranspose)*s.xi*V := by simp only [Matrix.mul_assoc]
    _=V.conjTranspose*(s.xi*s.xi)*V := by rw [hW.2,Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _=_ := by rw [s.xi_square]

theorem state_factor_cols {d : Nat} (V W : Mat d) (hV : IsUnitary V) (s : State d) :
    (V.conjTranspose*s.xi*W).conjTranspose*(V.conjTranspose*s.xi*W)=
      W.conjTranspose*s.rho*W := by
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,s.xi_positive.isHermitian.eq]
  calc
    _=W.conjTranspose*s.xi*(V*V.conjTranspose)*s.xi*W := by simp only [Matrix.mul_assoc]
    _=W.conjTranspose*(s.xi*s.xi)*W := by rw [hV.2,Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _=_ := by rw [s.xi_square]

theorem row_normSq {d : Nat} (B : Mat d) (i : Fin d) :
    (∑ j, Complex.normSq (B i j))=((B*B.conjTranspose) i i).re := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,
    Complex.mul_conj,Complex.re_sum,Complex.ofReal_re]

theorem col_normSq {d : Nat} (B : Mat d) (j : Fin d) :
    (∑ i, Complex.normSq (B i j))=((B.conjTranspose*B) j j).re := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,
    ←Complex.normSq_eq_conj_mul_self,Complex.re_sum,Complex.ofReal_re]

theorem spectral_cost {d : Nat} (P Q V W : Mat d) (z w : Fin d → ℂ) (s : State d)
    (hV : IsUnitary V) (hW : IsUnitary W)
    (hz : P=V*Matrix.diagonal z*V.conjTranspose)
    (hw : Q=W*Matrix.diagonal w*W.conjTranspose) :
    hs (P*s.xi-s.xi*Q)^2=
      ∑ i, ∑ j, Complex.normSq (z i-w j)*Complex.normSq ((V.conjTranspose*s.xi*W) i j) := by
  let B := V.conjTranspose*s.xi*W
  have hleft : V.conjTranspose*P=Matrix.diagonal z*V.conjTranspose := by
    rw [hz]
    calc
      _=(V.conjTranspose*V)*Matrix.diagonal z*V.conjTranspose := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hV.1,Matrix.one_mul]
  have hright : Q*W=W*Matrix.diagonal w := by
    rw [hw]
    calc
      _=W*Matrix.diagonal w*(W.conjTranspose*W) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hW.1,Matrix.mul_one]
  have hint : V.conjTranspose*(P*s.xi-s.xi*Q)*W=Matrix.diagonal z*B-B*Matrix.diagonal w := by
    simp only [Matrix.mul_sub,Matrix.sub_mul]
    calc
      _=(V.conjTranspose*P)*s.xi*W-V.conjTranspose*s.xi*(Q*W) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hleft,hright]; simp only [B,Matrix.mul_assoc]
  have hn : hsNorm (V.conjTranspose*(P*s.xi-s.xi*Q)*W)=hsNorm (P*s.xi-s.xi*Q) := by
    rw [hsNorm_unitary_right W _ hW.2,
      hsNorm_unitary_left V.conjTranspose _ (by simpa using hV.2)]
  rw [hint] at hn
  rw [hs_eq_hsNorm,←hn,hsNorm_sq]
  simp only [hsSquared,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show z i*B i j-B i j*w j=(z i-w j)*B i j by ring,Complex.normSq_mul]

theorem entrywise_abs_inner_le {d : Nat} (B D : Mat d) :
    (∑ i, ∑ j, ‖B i j‖*‖D i j‖)≤hs B*hs D := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ)
    (f:=fun ij : Fin d × Fin d => ‖B ij.1 ij.2‖)
    (g:=fun ij : Fin d × Fin d => ‖D ij.1 ij.2‖)
  simp only [Fintype.sum_prod_type] at hc
  have hb : (∑ i, ∑ j, ‖B i j‖^2)=hs B^2 := by
    rw [hs_eq_hsNorm,hsNorm_sq]
    simp only [hsSquared,Complex.normSq_eq_norm_sq]
  have hd : (∑ i, ∑ j, ‖D i j‖^2)=hs D^2 := by
    rw [hs_eq_hsNorm,hsNorm_sq]
    simp only [hsSquared,Complex.normSq_eq_norm_sq]
  rw [hb,hd] at hc
  apply (sq_le_sq₀ (by positivity : (0:ℝ)≤∑ i, ∑ j, ‖B i j‖*‖D i j‖)
    (mul_nonneg (show 0≤hs B from hsNorm_nonneg _) (show 0≤hs D from hsNorm_nonneg _))).mp
  simpa only [mul_pow] using hc

theorem abs_normSq_difference (b c : ℂ) :
    |Complex.normSq b-Complex.normSq c|≤(‖b‖+‖c‖)*‖b-c‖ := by
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,
    show ‖b‖^2-‖c‖^2=(‖b‖-‖c‖)*(‖b‖+‖c‖) by ring,abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le b c)
    (add_nonneg (norm_nonneg b) (norm_nonneg c))

theorem weighted_normSq_difference {d : Nat} (B C : Mat d) (f : Fin d → ℝ) (K : ℝ)
    (hK : 0≤K) (hf : ∀ i, |f i|≤K) :
    |∑ i, ∑ j, f j*(Complex.normSq (B i j)-Complex.normSq (C i j))|≤
      K*(hs B+hs C)*hs (B-C) := by
  calc
    _≤∑ i, ∑ j, |f j*(Complex.normSq (B i j)-Complex.normSq (C i j))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _≤∑ i, ∑ j, K*((‖B i j‖+‖C i j‖)*‖B i j-C i j‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hf j) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (abs_normSq_difference (B i j) (C i j)) hK)
    _=K*((∑ i, ∑ j, ‖B i j‖*‖(B-C) i j‖)+
        (∑ i, ∑ j, ‖C i j‖*‖(B-C) i j‖)) := by
      simp only [Matrix.sub_apply,add_mul,Finset.sum_add_distrib,←Finset.mul_sum]
    _≤K*(hs B*hs (B-C)+hs C*hs (B-C)) :=
      mul_le_mul_of_nonneg_left (add_le_add (entrywise_abs_inner_le B (B-C))
        (entrywise_abs_inner_le C (B-C))) hK
    _=_ := by ring

def conjugatedState {d : Nat} (U : Mat d) (hU : IsUnitary U) (s : State d) : State d where
  rho := U.conjTranspose*s.rho*U
  positive := s.positive.conjTranspose_mul_mul_same U
  normalized := by rw [Matrix.trace_mul_cycle,hU.2,Matrix.one_mul,s.normalized]
  xi := U.conjTranspose*s.xi*U
  xi_positive := s.xi_positive.conjTranspose_mul_mul_same U
  xi_square := by
    calc
      _=U.conjTranspose*s.xi*(U*U.conjTranspose)*s.xi*U := by simp only [Matrix.mul_assoc]
      _=U.conjTranspose*(s.xi*s.xi)*U := by rw [hU.2,Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _=_ := by rw [s.xi_square]

end
end Blueprint.W2
