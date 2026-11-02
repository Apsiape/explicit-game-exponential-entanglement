import Companion.AreaEstimate
import Companion.MatrixBlocks
import Mathlib.Tactic.Ring

namespace Companion
noncomputable section
open scoped BigOperators
open Analytic

def diagonalBlocks {α : Type*} (A B : Matrix α α ℂ) : Matrix (Bool × α) (Bool × α) ℂ :=
  fun (r,i) (s,j) => if s=r then (if r then B i j else A i j) else 0

theorem hsSquared_diagonalBlocks {α : Type*} [Fintype α] (A B : Matrix α α ℂ) :
    hsSquared (diagonalBlocks A B)=hsSquared A+hsSquared B := by
  simp [hsSquared,diagonalBlocks,Fintype.sum_prod_type,Fintype.sum_bool,
    Finset.sum_add_distrib,add_comm,add_left_comm,add_assoc]

theorem diagonalBlocks_sub_one {α : Type*} [Fintype α] [DecidableEq α] (A B : Matrix α α ℂ) :
    diagonalBlocks A B-1=diagonalBlocks (A-1) (B-1) := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> simp [diagonalBlocks,Matrix.one_apply,Prod.mk.injEq]

theorem normalized_diagonal_le {d : Nat} (hd : 0<d) (A B : Mat d) (eps : ℝ) (heps : 0≤eps)
    (hA : normalizedHS A≤eps) (hB : normalizedHS B≤eps) :
    hsNorm (diagonalBlocks A B)/Real.sqrt (2*(d:ℝ))≤eps := by
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hs : 0<Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdR
  have ht : 0<Real.sqrt (2*(d:ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hA' : hsNorm A≤eps*Real.sqrt (d:ℝ) :=
    (div_le_iff₀ hs).mp (by simpa [normalizedHS,div_eq_mul_inv,mul_comm] using hA)
  have hB' : hsNorm B≤eps*Real.sqrt (d:ℝ) :=
    (div_le_iff₀ hs).mp (by simpa [normalizedHS,div_eq_mul_inv,mul_comm] using hB)
  apply (div_le_iff₀ ht).mpr
  apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg heps ht.le)).mp
  calc
    (hsNorm (diagonalBlocks A B))^2 = (hsNorm A)^2+(hsNorm B)^2 := by
      rw [hsNorm_sq,hsSquared_diagonalBlocks,hsNorm_sq,hsNorm_sq]
    _ ≤ (eps*Real.sqrt (d:ℝ))^2+(eps*Real.sqrt (d:ℝ))^2 :=
      add_le_add ((sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg heps hs.le)).mpr hA')
        ((sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg heps hs.le)).mpr hB')
    _ = (eps*Real.sqrt (2*(d:ℝ)))^2 := by
      simp only [mul_pow,Real.sq_sqrt hdR.le,Real.sq_sqrt (show (0:ℝ)≤2*d by positivity)]
      ring

theorem gadget_block_defect {d : Nat} (phi : FreeGroup Nat →* Matrix.unitaryGroup (Fin d) ℂ)
    (eps : ℝ) (heps : 0≤eps)
    (hr : ∀ k r, gadgetBaseRelator k=some r →
      normalizedHS ((phi (FreeGroup.mk r):Mat d)-1)≤eps) :
    ∀ w ∈ gadgetBlockWords, normalizedHS ((phi (FreeGroup.mk w):Mat d)-1)≤3*eps := by
  intro w hw
  exact (gadget_block_areas w hw).length_bound (unitaryHSLength d) phi eps heps hr

/-- The local gadget's doubled matrix has normalized Hilbert--Schmidt
defect at most three times the input defect, with no scalar assumption
standing in for the norm estimate. -/
theorem gadget_doubled_defect {d : Nat} (hd : 0<d)
    (phi : FreeGroup Nat →* Matrix.unitaryGroup (Fin d) ℂ) (eps : ℝ) (heps : 0≤eps)
    (hr : ∀ k r, gadgetBaseRelator k=some r → normalizedHS ((phi (FreeGroup.mk r):Mat d)-1)≤eps) :
    ∀ r ∈ gadgetBlockRelators,
      hsNorm (interpretBlock (coeUnitaryHom phi) (evalBlock r)-1)/Real.sqrt (2*(d:ℝ))≤3*eps := by
  intro r hmem
  have hdiag : (evalBlock r).swapped=false := by
    have h := List.all_eq_true.mp gadget_blocks_diagonal r hmem
    simpa using h
  have hfirst : (evalBlock r).first ∈ gadgetBlockWords :=
    List.mem_flatMap.mpr ⟨r,hmem,by simp⟩
  have hsecond : (evalBlock r).second ∈ gadgetBlockWords :=
    List.mem_flatMap.mpr ⟨r,hmem,by simp⟩
  have he : interpretBlock (coeUnitaryHom phi) (evalBlock r)=
      diagonalBlocks (matrixWord (coeUnitaryHom phi) (evalBlock r).first)
        (matrixWord (coeUnitaryHom phi) (evalBlock r).second) := by
    apply Matrix.ext
    rintro ⟨b,i⟩ ⟨c,j⟩
    cases b <;> cases c <;> simp [interpretBlock,diagonalBlocks,hdiag]
  rw [he,diagonalBlocks_sub_one]
  apply normalized_diagonal_le hd _ _ (3*eps) (by positivity)
  · exact gadget_block_defect phi eps heps hr _ hfirst
  · exact gadget_block_defect phi eps heps hr _ hsecond

end
end Companion
