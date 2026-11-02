import Companion.ProjectiveCoarseGraining
import QIT.Measurements.Naimark

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem strategy_valid_answer_exists {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) : ∃ a, validAnswer g i a := by
  have hn : hsNorm s.psi.conjTranspose=1 := by rw [hsNorm_conjTranspose]; exact s.normalized
  letI : Nonempty (Fin dA) := (CountProof.factorState s.psi.conjTranspose hn).nonempty
  by_contra h
  have hz (a : Fin g.system.n → Bool) : s.alice i a=0 :=
    s.alice_valid i a (fun ha => h ⟨a,ha⟩)
  have he : (0:Mat dA)=1 := by simpa only [hz,Finset.sum_const_zero] using s.alice_complete i
  exact zero_ne_one he

def selectedValidAnswer {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (i : Fin g.system.equations.length) :
    Fin g.system.n → Bool := Classical.choose (strategy_valid_answer_exists s i)

theorem selectedValidAnswer_valid {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) : validAnswer g i (selectedValidAnswer s i) :=
  Classical.choose_spec (strategy_valid_answer_exists s i)

def alicePOVM {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (i : Fin g.system.equations.length) :
    QIT.POVM (Fin g.system.n → Bool) (Fin dA) :=
  ⟨s.alice i,s.alice_positive i,s.alice_complete i⟩

abbrev AliceDilationSpace {g : LCS} (dA : Nat) := Fin dA × (Fin g.system.n → Bool)

def aliceDilationEmbedding {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    Matrix (AliceDilationSpace (g:=g) dA) (Fin dA) ℂ :=
  QIT.POVM.familyNaimarkEmbedding (alicePOVM s)

theorem aliceDilationEmbedding_isometry {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    (aliceDilationEmbedding s).conjTranspose*aliceDilationEmbedding s=1 :=
  QIT.POVM.familyNaimarkEmbedding_isometry (alicePOVM s)

/-- Invalid Naimark outcomes are redirected to a selected valid answer.
The resulting global projectors vanish on every invalid answer. -/
def aliceDilationPVM {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) :
    QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (AliceDilationSpace (g:=g) dA) := by
  classical
  exact coarsePVM (QIT.POVM.familyNaimarkProjectiveMeasurement (alicePOVM s) i)
    (validOutputMap (validAnswer g i) (selectedValidAnswer s i))

theorem aliceDilationPVM_valid {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) (ha : ¬validAnswer g i a) :
    (aliceDilationPVM s i).effects a=0 := by
  classical
  exact valid_coarseEffect_zero _ _ _ (selectedValidAnswer_valid s i) a ha

theorem aliceDilationPVM_compression {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) :
    (aliceDilationEmbedding s).conjTranspose*(aliceDilationPVM s i).effects a*aliceDilationEmbedding s=s.alice i a := by
  classical
  rw [aliceDilationPVM]
  change (aliceDilationEmbedding s).conjTranspose*coarseEffect _ _ a*aliceDilationEmbedding s=_
  rw [coarseEffect_compression]
  simp_rw [show ∀ b, (aliceDilationEmbedding s).conjTranspose*
      (QIT.POVM.familyNaimarkProjectiveMeasurement (alicePOVM s) i).effects b*aliceDilationEmbedding s=s.alice i b from
    fun b => QIT.POVM.familyNaimark_compression_projector_eq (alicePOVM s) i b]
  exact valid_coarse_original (s.alice i) (validAnswer g i) (s.alice_valid i) _ a

def reindexPVM {a b y : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype y]
    (P : QIT.ProjectiveMeasurement y a) (e : a ≃ b) : QIT.ProjectiveMeasurement y b where
  effects y := (P.effects y).submatrix e.symm e.symm
  isHermitian y := (P.isHermitian y).submatrix e.symm
  idempotent y := by rw [Matrix.submatrix_mul_equiv,P.idempotent y]
  orthogonal y z hyz := by rw [Matrix.submatrix_mul_equiv,P.orthogonal y z hyz]; rfl
  sum_eq_one := by
    have h : (∑ y, (P.effects y).submatrix e.symm e.symm)=(∑ y, P.effects y).submatrix e.symm e.symm := by
      ext i j
      simp only [Matrix.sum_apply,Matrix.submatrix_apply]
    rw [h,P.sum_eq_one]
    exact Matrix.submatrix_one_equiv e.symm

def aliceFiniteEmbedding {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    Matrix (Fin (Fintype.card (AliceDilationSpace (g:=g) dA))) (Fin dA) ℂ :=
  (aliceDilationEmbedding s).submatrix (Fintype.equivFin _).symm id

theorem aliceFiniteEmbedding_isometry {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    (aliceFiniteEmbedding s).conjTranspose*aliceFiniteEmbedding s=1 := by
  rw [aliceFiniteEmbedding,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id,aliceDilationEmbedding_isometry]

def aliceFinitePVM {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (i : Fin g.system.equations.length) :
    QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin (Fintype.card (AliceDilationSpace (g:=g) dA))) :=
  reindexPVM (aliceDilationPVM s i) (Fintype.equivFin _)

theorem aliceFinitePVM_valid {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) (ha : ¬validAnswer g i a) :
    (aliceFinitePVM s i).effects a=0 := by
  change ((aliceDilationPVM s i).effects a).submatrix _ _=0
  rw [aliceDilationPVM_valid s i a ha]; rfl

theorem aliceFinitePVM_compression {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) :
    (aliceFiniteEmbedding s).conjTranspose*(aliceFinitePVM s i).effects a*aliceFiniteEmbedding s=s.alice i a := by
  change ((aliceDilationEmbedding s).submatrix _ id).conjTranspose*
    ((aliceDilationPVM s i).effects a).submatrix _ _*(aliceDilationEmbedding s).submatrix _ id=_
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
  exact aliceDilationPVM_compression s i a

end
end Companion.Analytic.TransferProof
