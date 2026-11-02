import Companion.HilbertSchmidt
import Companion.GadgetBlocks

namespace Companion
noncomputable section
open scoped BigOperators

def matrixWord {d : Nat} (phi : FreeGroup Nat →* Analytic.Mat d) (w : Word) : Analytic.Mat d :=
  phi (FreeGroup.mk w)

def interpretBlock {d : Nat} (phi : FreeGroup Nat →* Analytic.Mat d) (b : WordBlock) :
    Matrix (Bool × Fin d) (Bool × Fin d) ℂ :=
  fun (r,i) (s,j) => if s=(r ^^ b.swapped) then matrixWord phi (if r then b.second else b.first) i j else 0

theorem matrixWord_append {d : Nat} (phi : FreeGroup Nat →* Analytic.Mat d) (u v : Word) :
    matrixWord phi (u++v)=matrixWord phi u*matrixWord phi v := by
  simp [matrixWord,← FreeGroup.mul_mk]

theorem interpretBlock_mul {d : Nat} (phi : FreeGroup Nat →* Analytic.Mat d) (a b : WordBlock) :
    interpretBlock phi (blockMul a b)=interpretBlock phi a*interpretBlock phi b := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> cases ha : a.swapped <;> cases hb : b.swapped
  all_goals simp [interpretBlock,blockMul,ha,hb,matrixWord_append,Matrix.mul_apply,
    Fintype.sum_prod_type,Fintype.sum_bool]

theorem interpretBlock_identity {d : Nat} (phi : FreeGroup Nat →* Analytic.Mat d) :
    interpretBlock phi ⟨false,[],[]⟩=1 := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;>
    simp [interpretBlock,matrixWord,← FreeGroup.one_eq_mk,Matrix.one_apply,Prod.mk.injEq]

theorem interpretBlock_inverse_left {d : Nat} (phi : FreeGroup Nat →* Analytic.Mat d) (b : WordBlock) :
    interpretBlock phi (blockInv b)*interpretBlock phi b=1 := by
  rw [← interpretBlock_mul]
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> cases hb : b.swapped
  all_goals simp [interpretBlock,blockMul,blockInv,hb,matrixWord,
    ← FreeGroup.mul_mk,← FreeGroup.inv_mk,← map_mul,Matrix.one_apply,Prod.mk.injEq]

theorem interpretBlock_inverse_right {d : Nat} (phi : FreeGroup Nat →* Analytic.Mat d) (b : WordBlock) :
    interpretBlock phi b*interpretBlock phi (blockInv b)=1 := by
  rw [← interpretBlock_mul]
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> cases hb : b.swapped
  all_goals simp [interpretBlock,blockMul,blockInv,hb,matrixWord,
    ← FreeGroup.mul_mk,← FreeGroup.inv_mk,← map_mul,Matrix.one_apply,Prod.mk.injEq]

def coeUnitaryHom {d : Nat} (phi : FreeGroup Nat →* Matrix.unitaryGroup (Fin d) ℂ) :
    FreeGroup Nat →* Analytic.Mat d := (Matrix.unitaryGroup (Fin d) ℂ).subtype.comp phi

theorem matrixWord_invRev {d : Nat} (phi : FreeGroup Nat →* Matrix.unitaryGroup (Fin d) ℂ) (w : Word) :
    matrixWord (coeUnitaryHom phi) (FreeGroup.invRev w)=
      (matrixWord (coeUnitaryHom phi) w).conjTranspose := by
  simp [matrixWord,coeUnitaryHom,← FreeGroup.inv_mk,Matrix.star_eq_conjTranspose]

theorem interpretBlock_conjTranspose {d : Nat} (phi : FreeGroup Nat →* Matrix.unitaryGroup (Fin d) ℂ)
    (b : WordBlock) : (interpretBlock (coeUnitaryHom phi) b).conjTranspose=
      interpretBlock (coeUnitaryHom phi) (blockInv b) := by
  apply Matrix.ext
  rintro ⟨r,i⟩ ⟨s,j⟩
  cases r <;> cases s <;> cases hb : b.swapped
  all_goals simp [interpretBlock,blockInv,hb,matrixWord_invRev,Matrix.conjTranspose_apply]

def blockAsUnitary {d : Nat} (phi : FreeGroup Nat →* Matrix.unitaryGroup (Fin d) ℂ) (b : WordBlock) :
    Matrix.unitaryGroup (Bool × Fin d) ℂ :=
  ⟨interpretBlock (coeUnitaryHom phi) b, by
    change (interpretBlock (coeUnitaryHom phi) b).conjTranspose * interpretBlock (coeUnitaryHom phi) b = 1 ∧
      interpretBlock (coeUnitaryHom phi) b * (interpretBlock (coeUnitaryHom phi) b).conjTranspose=1
    rw [interpretBlock_conjTranspose]
    exact ⟨interpretBlock_inverse_left _ _,interpretBlock_inverse_right _ _⟩⟩

theorem doubled_dimension (d : Nat) : Fintype.card (Bool × Fin d)=2*d := by simp
theorem eightfold_dimension (d : Nat) : Fintype.card (Bool × Bool × Bool × Fin d)=8*d := by simp; omega

end
end Companion
