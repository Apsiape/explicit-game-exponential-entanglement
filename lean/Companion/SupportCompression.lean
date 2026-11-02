import Companion.UniformCountTheorem
import Companion.StrategyEncoding

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

theorem support_card_eq_rank {a : Type*} [Fintype a] [DecidableEq a]
    (rho : QIT.State a) : Fintype.card (QIT.psdSupportIndex rho.matrix rho.pos)=rho.matrix.rank := by
  rw [rho.pos.isHermitian.rank_eq_card_non_zero_eigs]
  apply Fintype.card_congr
  unfold QIT.psdSupportIndex
  exact Equiv.subtypeEquivRight (fun i =>
    ⟨ne_of_gt,fun h => lt_of_le_of_ne (rho.pos.eigenvalues_nonneg i) (Ne.symm h)⟩)

/-- Compression to exactly the spectral support, expressed on Fin r.
The isometry reconstructs the original density matrix and its entropy. -/
theorem finite_support_compression {d : Nat} (rho : QIT.State (Fin d)) :
    ∃ (r : Nat) (sigma : QIT.State (Fin r)) (V : Matrix (Fin d) (Fin r) ℂ),
      r=rho.matrix.rank ∧ 0<r ∧ r≤d ∧ sigma.matrix.PosDef ∧
      V.conjTranspose*V=1 ∧ V*sigma.matrix*V.conjTranspose=rho.matrix ∧
      sigma.vonNeumann=rho.vonNeumann := by
  let S := QIT.psdSupportIndex rho.matrix rho.pos
  let r := Fintype.card S
  let e : S ≃ Fin r := Fintype.equivFin S
  let rhoC := QIT.psdSupportCompressedState rho rho.pos (QIT.Matrix.Supports.refl rho.matrix)
  let U := QIT.psdSupportIsometry rho.matrix rho.pos
  let V := U.submatrix id e.symm
  let sigma := rhoC.reindex e
  have hr : r=rho.matrix.rank := support_card_eq_rank rho
  have hU : U.conjTranspose*U=1 := QIT.psdSupportIsometry_isometry rho.matrix rho.pos
  have hV : V.conjTranspose*V=1 := by
    change (U.submatrix id e.symm).conjTranspose*U.submatrix id e.symm=1
    rw [Matrix.conjTranspose_submatrix]
    change U.conjTranspose.submatrix e.symm (Equiv.refl (Fin d))*
      U.submatrix (Equiv.refl (Fin d)) e.symm=1
    rw [Matrix.submatrix_mul_equiv,hU]
    exact Matrix.submatrix_one_equiv e.symm
  have hrec : V*sigma.matrix*V.conjTranspose=rho.matrix := by
    change U.submatrix id e.symm*rhoC.matrix.submatrix e.symm e.symm*(U.submatrix id e.symm).conjTranspose=_
    rw [Matrix.submatrix_mul_equiv,Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
    exact QIT.psdSupportCompress_reconstruct_self rho.matrix rho.pos
  have hpd : sigma.matrix.PosDef :=
    (QIT.psdSupportCompress_self_posDef rho.matrix rho.pos).submatrix e.symm.injective
  have hp : 0<r := Fintype.card_pos_iff.mpr
    (QIT.psdSupportCompressedState_support_nonempty rho rho.pos (QIT.Matrix.Supports.refl rho.matrix))
  have hent : sigma.vonNeumann=rho.vonNeumann :=
    (quair_entropy_isometry sigma rho V hV hrec.symm).symm
  exact ⟨r,sigma,V,hr,hp,hr.trans_le rho.matrix.rank_le_width,hpd,hV,hrec,hent⟩

/-- The dimension in the support compression of a bipartite pure state
is its Schmidt rank and is bounded by both original local dimensions. -/
theorem schmidt_support_compression {dA dB : Nat}
    (psi : Matrix (Fin dB) (Fin dA) ℂ) (hn : hsNorm psi=1) :
    ∃ (r : Nat) (sigma : QIT.State (Fin r)) (V : Matrix (Fin dB) (Fin r) ℂ),
      r=psi.rank ∧ 0<r ∧ r≤dA ∧ r≤dB ∧ sigma.matrix.PosDef ∧
      V.conjTranspose*V=1 ∧ V*sigma.matrix*V.conjTranspose=psi*psi.conjTranspose ∧
      sigma.vonNeumann=(CountProof.factorState psi hn).vonNeumann := by
  obtain ⟨r,sigma,V,hr,hp,hB,hpd,hV,hrec,hent⟩ := finite_support_compression (CountProof.factorState psi hn)
  have hrank : r=psi.rank := hr.trans (Matrix.rank_self_mul_conjTranspose psi)
  exact ⟨r,sigma,V,hrank,hp,hrank.trans_le psi.rank_le_width,hB,hpd,hV,hrec,hent⟩

end
end Companion.Analytic.TransferProof
