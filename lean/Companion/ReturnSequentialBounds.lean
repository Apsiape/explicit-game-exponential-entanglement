import Companion.SequentialMismatch
import Companion.RecordParity

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open TransferProof
set_option maxHeartbeats 600000

theorem transpose_state_commutator_norm {d : Nat} (B xi : Mat d) :
    hsNorm (comm B.transpose xi.transpose)=hsNorm (comm B xi) := by
  rw [← hsNorm_transpose (comm B.transpose xi.transpose)]
  have he : (comm B.transpose xi.transpose).transpose= -(comm B xi) := by
    simp only [comm,Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_transpose]
    abel
  rw [he]
  simp only [hsNorm_eq_frobenius,norm_neg]

theorem transpose_pair_commutator_norm {d : Nat} (B C xi : Mat d)
    (hB : IsInvolution B) (hC : IsInvolution C) (hxi : xi.IsHermitian) :
    hsNorm (comm B.transpose C.transpose*xi.transpose)=hsNorm (comm B C*xi) := by
  rw [← hsNorm_transpose (comm B.transpose C.transpose*xi.transpose)]
  have he : (comm B.transpose C.transpose*xi.transpose).transpose=(comm B C*xi).conjTranspose := by
    simp only [comm,Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_transpose,
      Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,hB.1,hC.1,hxi.eq]
  rw [he,hsNorm_conjTranspose]

def rowBob {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j : Fin (g.system.equations[i.val]).vars.length) : Mat d :=
  roundedGenerators m (rowIndex g i j)

def rowKraus {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) : (Fin (g.system.equations[i.val]).vars.length → Bool) → Mat d :=
  CountProof.jointProjection _ (fun j => (rowBob m i j).transpose)

def rowFactor {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (a : Fin (g.system.equations[i.val]).vars.length → Bool) : Mat d :=
  m.state.xi*(rowKraus m i a).transpose

def rowError {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j : Fin (g.system.equations[i.val]).vars.length) : ℝ :=
  familyHS (fun a => rowBob m i j*rowFactor m i a-boolPhase (a j) • rowFactor m i a)

theorem rowError_eq_mismatch {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j : Fin (g.system.equations[i.val]).vars.length) :
    rowError m i j=sequentialMismatch (fun j => (rowBob m i j).transpose) m.state.xi.transpose j := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  simp only [rowError,sequentialMismatch,familyHS_sq]
  apply Finset.sum_congr rfl
  intro a _
  rw [← hsNorm_transpose]
  have he : (rowBob m i j*rowFactor m i a-boolPhase (a j) • rowFactor m i a).transpose=
      -(boolPhase (a j) • (rowKraus m i a*m.state.xi.transpose)-
        rowKraus m i a*m.state.xi.transpose*(rowBob m i j).transpose) := by
    simp only [rowFactor,Matrix.transpose_sub,Matrix.transpose_smul,Matrix.transpose_mul,
      Matrix.transpose_transpose,Matrix.mul_assoc]
    abel
  rw [he]
  simp only [hsNorm_eq_frobenius,norm_neg]
  rfl

theorem rowError_bound {g : LCS} {d : Nat} {e : ℝ} (m : Model g d e)
    (i : Fin g.system.equations.length) (j : Fin (g.system.equations[i.val]).vars.length) :
    rowError m i j≤nu (j.val+1)*e := by
  rw [rowError_eq_mismatch]
  have hB (j) : IsInvolution (rowBob m i j) := roundedGenerators_involution m _
  have hc (j) : hsNorm (comm (rowBob m i j).transpose m.state.xi.transpose)≤3*e := by
    rw [transpose_state_commutator_norm]
    exact (rounded_generators_estimates m _).2
  have hk (j l) : hsNorm (comm (rowBob m i j).transpose (rowBob m i l).transpose*m.state.xi.transpose)≤13*e := by
    rw [transpose_pair_commutator_norm _ _ _ (hB j) (hB l) m.state.xi_positive.isHermitian]
    exact rounded_commutator_bound m i _ _ (List.getElem_mem j.isLt) (List.getElem_mem l.isLt)
  have h := sequential_mismatch_uniform _ (fun j => (rowBob m i j).transpose)
    (fun j => transpose_involution _ (hB j)) m.state.xi.transpose (3*e) (13*e) hc hk j
  calc
    _≤3*e+(j.val:ℝ)*(13*e)/Real.sqrt 2+(j.val:ℝ)*((j.val:ℝ)-1)*(3*e)/2 := h
    _=nu (j.val+1)*e := by unfold nu; push_cast; ring

end
end Companion.Analytic.ReturnProof
