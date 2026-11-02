import Blueprint.A.PauliRelations

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem pauli_sector_bounds {d : Nat} (hd : 0<d) (s t : State d) (J X Z : Mat d)
    (hJ : IsInvolution J) (hX : IsInvolution X) (hZ : IsInvolution Z)
    (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : hs (t.xi-((Real.sqrt (signProjection J true*s.rho).trace.re)⁻¹:ℂ) •
      (signProjection J true*s.xi*signProjection J true))≤
      hs (comm J s.xi)/(2*Real.sqrt (signProjection J true*s.rho).trace.re))
    (G C CJ : ℝ) (hG : hs ((X*Z*X*Z-J)*s.xi)≤G)
    (hCX : hs (comm X s.xi)≤C) (hCZ : hs (comm Z s.xi)≤C)
    (hCJ : hs (comm J s.xi)≤CJ) :
    hs (comm X t.xi)≤(2*G+6*C+3*CJ)/Real.sqrt (signProjection J true*s.rho).trace.re ∧
    hs (comm Z t.xi)≤(2*G+6*C+3*CJ)/Real.sqrt (signProjection J true*s.rho).trace.re ∧
    hs (anti X Z*t.xi)≤(9*G+24*C+15*CJ)/Real.sqrt (signProjection J true*s.rho).trace.re := by
  let K := X*Z*X*Z
  let q := Real.sqrt (signProjection J true*s.rho).trace.re
  have hq : 0<q := Real.sqrt_pos.mpr hp
  have hXu := CountProof.involution_unitary X hX
  have hZu := CountProof.involution_unitary Z hZ
  have hK : IsUnitary K := ReturnProof.unitary_mul _ _
    (ReturnProof.unitary_mul _ _ (ReturnProof.unitary_mul _ _ hXu hZu) hXu) hZu
  have hXK : X*K*X=K.conjTranspose := by
    simp only [K,Matrix.conjTranspose_mul,hX.1,hZ.1]
    calc
      _=(X*X)*Z*X*Z*X := by simp only [Matrix.mul_assoc]
      _=_ := by simp only [hX.2,Matrix.one_mul,Matrix.mul_assoc]
  have hZK : Z*K*Z=K.conjTranspose := by
    simp only [K,Matrix.conjTranspose_mul,hX.1,hZ.1]
    calc
      _=Z*X*Z*X*(Z*Z) := by simp only [Matrix.mul_assoc]
      _=_ := by simp only [hZ.2,Matrix.mul_one,Matrix.mul_assoc]
  have hXJ := marker_commutator X K J s.xi hX hK hJ hXK G C CJ hG hCX hCJ
  have hZJ := marker_commutator Z K J s.xi hZ hK hJ hZK G C CJ hG hCZ hCJ
  have htx := SV.sector_commutator_bound s t X J hXu hJ hp ht
  have htz := SV.sector_commutator_bound s t Z J hZu hJ hp ht
  have hX' : hs (comm X t.xi)≤(2*G+6*C+3*CJ)/q := by
    apply htx.trans
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have hZ' : hs (comm Z t.xi)≤(2*G+6*C+3*CJ)/q := by
    apply htz.trans
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  refine ⟨hX',hZ',?_⟩
  have hm := SV.sector_marker_bound hd s t K J hK hJ hp ht
  have hm' : hs ((K+1)*t.xi)≤(G+3*CJ)/q := by
    apply hm.trans
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have hV := ReturnProof.unitary_mul Z X hZu hXu
  have hcV := ReturnProof.unitary_product_commutator Z X t.xi hZu hXu
  have hneg : IsUnitary (-1:Mat d) := by simp [IsUnitary]
  have hmV := ReturnProof.unitary_difference_right_transport K (-1) (Z*X) t.xi hK hneg hV
  have hcancel : K*(Z*X)=X*Z := by
    calc
      _=X*Z*X*(Z*Z)*X := by simp only [K,Matrix.mul_assoc]
      _=X*Z := by simp only [hZ.2,Matrix.mul_one,Matrix.mul_assoc,hX.2,Matrix.mul_one]
  have he : (K-(-1))*(Z*X)=anti X Z := by
    rw [sub_neg_eq_add,Matrix.add_mul,hcancel,Matrix.one_mul]
    rfl
  rw [he,sub_neg_eq_add] at hmV
  change hs (anti X Z*t.xi)≤(9*G+24*C+15*CJ)/q
  have heq : (G+3*CJ)/q+4*((2*G+6*C+3*CJ)/q)=(9*G+24*C+15*CJ)/q := by ring
  rw [←heq]
  simp only [hs_eq_hsNorm] at *
  linarith

theorem cross_sector_bound {d : Nat} (hd : 0<d) (s t : State d) (J X Z : Mat d)
    (hJ : IsInvolution J) (hX : IsUnitary X) (hZ : IsUnitary Z)
    (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : hs (t.xi-((Real.sqrt (signProjection J true*s.rho).trace.re)⁻¹:ℂ) •
      (signProjection J true*s.xi*signProjection J true))≤
      hs (comm J s.xi)/(2*Real.sqrt (signProjection J true*s.rho).trace.re))
    (E CJ : ℝ) (hE : hs (comm X Z*s.xi)≤E) (hCJ : hs (comm J s.xi)≤CJ) :
    hs (comm X Z*t.xi)≤(E+2*CJ)/Real.sqrt (signProjection J true*s.rho).trace.re := by
  have hh := SV.sector_weighted_bound s t J hJ hp ht (comm X Z)
  have hn : ‖comm X Z‖≤2 := SV.difference_operator_norm hd _ _
    (ReturnProof.unitary_mul X Z hX hZ) (ReturnProof.unitary_mul Z X hZ hX)
  have hm := mul_le_mul_of_nonneg_right hn (hsNorm_nonneg (comm J s.xi))
  have hq : 0≤Real.sqrt (signProjection J true*s.rho).trace.re := Real.sqrt_nonneg _
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hq
  simp only [hs_eq_hsNorm] at *
  linarith

end
end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.pauli_sector_bounds
#print axioms Blueprint.ASectorProof.cross_sector_bound
