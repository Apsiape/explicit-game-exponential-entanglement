import Blueprint.A.SectorState

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic Companion.Analytic.CountProof
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

/-- A normalized compression contributes its probability times its entropy
to the entropy of the two-sector pinching, including a zero complementary block. -/
theorem sector_pinching_entropy_lower {d : Nat} (s t : State d) (J : Mat d)
    (hJ : IsInvolution J) (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : t.rho=(((signProjection J true*s.rho).trace.re:ℂ)⁻¹) •
      (signProjection J true*s.rho*signProjection J true)) :
    (signProjection J true*s.rho).trace.re*entropy t.rho ≤
      (pinchingState J hJ s.toQuAIR).vonNeumann := by
  let P := symmetryProjection J
  let B := fun i : Bool => P i*s.rho*P i
  let p := fun i : Bool => (B i).trace.re
  let sigma := pinchingState J hJ s.toQuAIR
  have hh : ∀ i, (P i).conjTranspose=P i := symmetryProjection_hermitian J hJ.1
  have hm : ∀ i j, P i*P j=if i=j then P i else 0 := symmetryProjection_mul J hJ.2
  have hP : ∑ i, (P i).conjTranspose*P i=1 := symmetryProjection_complete J hJ
  have hB : ∀ i, (B i).PosSemidef := fun i => by
    simpa only [B,hh i] using s.positive.mul_mul_conjTranspose_same (P i)
  have hsigma : sigma.matrix=∑ i, B i := by
    change (∑ i, P i*s.rho*(P i).conjTranspose)=_
    simp only [hh,B]
  have hpsum : ∑ i, p i=1 := by
    have he := congrArg (fun A : Mat d => A.trace.re) hsigma
    simpa only [Fintype.sum_bool,Matrix.trace_add,Complex.add_re,sigma.trace_eq_one,Complex.one_re,p] using he.symm
  have hp0 : ∀ i, 0≤p i := fun i => (hB i).trace_nonneg.1
  have hp1 : ∀ i, p i≤1 := by
    intro i
    rw [Fintype.sum_bool] at hpsum
    cases i <;> have hf := hp0 false <;> have ht := hp0 true <;> linarith
  let V := readoutIsometry P
  let tau := isometryState sigma V (readoutIsometry_isometry P hP)
  have hTau : tau.matrix=Matrix.blockDiagonal B := by
    ext ⟨i,a⟩ ⟨j,b⟩
    change (readoutIsometry P*sigma.matrix*(readoutIsometry P).conjTranspose) (i,a) (j,b)=_
    rw [readoutIsometry_matrix,hh b,hsigma,orthogonal_sandwich P hm]
    by_cases he : a=b
    · subst b; simp [B,Matrix.blockDiagonal_apply]
    · simp [B,he,Ne.symm he,Matrix.blockDiagonal_apply]
  let T := fun i => normalizedBlock (B i) (hB i) s.toQuAIR
  have hscale : tau.matrix=Matrix.blockDiagonal (fun i => (p i:ℂ) • (T i).matrix) := by
    simpa only [T,p,normalizedBlock_scale] using hTau
  have he := QIT.State.vonNeumann_eq_shannon_add_average_of_blockDiagonal tau p T hp0 hscale
  rw [isometryState_entropy] at he
  have hclassical : 0≤-(∑ i, QIT.xlog2 (p i)) := by
    have hn : 0≤(∑ i, Real.negMulLog (p i))/Real.log 2 :=
      div_nonneg (Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hp0 i) (hp1 i)))
        (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    simpa only [Finset.sum_div,negMulLog_bits,Finset.sum_neg_distrib] using hn
  have hcomplement : 0≤p false*(T false).vonNeumann :=
    mul_nonneg (hp0 false) (T false).vonNeumann_nonneg
  have hptrace : p true=(signProjection J true*s.rho).trace.re := by
    change (symmetryProjection J true*s.rho*symmetryProjection J true).trace.re=
      (symmetryProjection J true*s.rho).trace.re
    rw [Matrix.trace_mul_cycle,symmetryProjection_square J hJ.2 true]
  have hT : T true=t.toQuAIR := by
    apply QIT.State.ext
    dsimp only [T,normalizedBlock]
    rw [dite_eq_right (by change p true≠0; rw [hptrace]; exact hp.ne'),
      QIT.State.normalizePSD_matrix]
    change (p true)⁻¹ • B true=t.rho
    rw [hptrace]
    convert ht.symm using 1
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,Complex.ofReal_inv,smul_eq_mul]
    rfl
  simp only [Fintype.sum_bool] at he hclassical
  rw [hT,←entropy_eq_quair t,hptrace] at he
  rw [hptrace] at hclassical
  change _≤sigma.vonNeumann
  linarith

/-- Compression cannot increase matrix rank, with the statement's rank convention. -/
theorem sector_compression_rank {d : Nat} (s t : State d) (P : Mat d) (c : ℂ)
    (ht : t.rho=c • (P*s.rho*P)) : rank t.rho≤rank s.rho := by
  change t.rho.rank≤s.rho.rank
  rw [ht]
  have he : c • (P*s.rho*P)=(c • (1:Mat d))*(P*s.rho*P) := by simp
  rw [he]
  exact (Matrix.rank_mul_le_right _ _).trans
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))

/-- Lemma 4.7 with its full binary-entropy correction and rank conclusion. -/
theorem sector_entropy_from_pinching {d : Nat} (s t : State d) (J : Mat d)
    (hJ : IsInvolution J) (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : t.rho=(((signProjection J true*s.rho).trace.re:ℂ)⁻¹) •
      (signProjection J true*s.rho*signProjection J true)) :
    (signProjection J true*s.rho).trace.re*entropy t.rho-
      binaryEntropy (min (hs (comm J s.xi)^2/4) (1/2))≤entropy s.rho ∧
      rank t.rho≤rank s.rho := by
  have hnorm : hsNorm s.xi=1 := ReturnProof.state_xi_normalized s
  let U : Matrix.unitaryGroup (Fin d) ℂ := ⟨J,involution_unitary J hJ⟩
  have hfactor : factorState s.xi hnorm=s.toQuAIR := by
    apply QIT.State.ext
    change s.xi*s.xi.conjTranspose=s.rho
    rw [s.xi_positive.isHermitian.eq,s.xi_square]
  have hdist : hsNorm (s.xi*(U:Mat d)-J*s.xi)≤hs (comm J s.xi) := by
    open scoped Matrix.Norms.Frobenius in
    change hsNorm (s.xi*J-J*s.xi)≤hsNorm (J*s.xi-s.xi*J)
    rw [←neg_sub (J*s.xi) (s.xi*J)]
    simp only [hsNorm_eq_frobenius,norm_neg,le_refl]
  have hu := pinching_factor_bound J hJ s.xi hnorm U (hs (comm J s.xi))
    (hsNorm_nonneg _) hdist
  rw [hfactor,←entropy_eq_quair s] at hu
  have hl := sector_pinching_entropy_lower s t J hJ hp ht
  exact ⟨by linarith,sector_compression_rank s t _ _ ht⟩

end
end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.sector_pinching_entropy_lower
#print axioms Blueprint.ASectorProof.sector_compression_rank
#print axioms Blueprint.ASectorProof.sector_entropy_from_pinching
