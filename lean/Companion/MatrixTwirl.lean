import Companion.Twirl
import Companion.HilbertSchmidt

namespace Companion.Analytic
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 400000

abbrev HSSpace (d : Nat) := EuclideanSpace ℂ (Fin d × Fin d)

def hsVector {d : Nat} (A : Mat d) : HSSpace d := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
def hsMatrix {d : Nat} (v : HSSpace d) : Mat d := fun i j => v (i,j)

@[simp] theorem hsMatrix_vector {d : Nat} (A : Mat d) : hsMatrix (hsVector A)=A := rfl
@[simp] theorem hsVector_matrix {d : Nat} (v : HSSpace d) : hsVector (hsMatrix v)=v := rfl
theorem hsVector_sub {d : Nat} (A B : Mat d) : hsVector (A-B)=hsVector A-hsVector B := rfl
theorem hsVector_add {d : Nat} (A B : Mat d) : hsVector (A+B)=hsVector A+hsVector B := rfl
theorem hsVector_neg {d : Nat} (A : Mat d) : hsVector (-A)= -hsVector A := rfl

def hsVectorEquiv (d : Nat) : Mat d ≃ₗ[ℂ] HSSpace d where
  toFun := hsVector
  invFun := hsMatrix
  left_inv := hsMatrix_vector
  right_inv := hsVector_matrix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hsVector_norm {d : Nat} (A : Mat d) : ‖hsVector A‖=hsNorm A := by
  apply (sq_eq_sq₀ (norm_nonneg _) (hsNorm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,hsNorm_sq]
  simp only [Fintype.sum_prod_type,hsVector,hsSquared,Complex.normSq_eq_norm_sq]

theorem hsMatrix_norm {d : Nat} (v : HSSpace d) : hsNorm (hsMatrix v)=‖v‖ := by
  simpa only [hsVector_matrix] using (hsVector_norm (hsMatrix v)).symm

def matrixConjugation {d : Nat} (Z : Mat d) : Mat d →ₗ[ℂ] Mat d where
  toFun v := Z*v*Z
  map_add' v w := by simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' a v := by simp [Matrix.mul_smul,Matrix.smul_mul]

def conjugationOp {d : Nat} (Z : Mat d) : HSSpace d →ₗ[ℝ] HSSpace d :=
  (((hsVectorEquiv d).toLinearMap.comp (matrixConjugation Z)).comp
    (hsVectorEquiv d).symm.toLinearMap).restrictScalars ℝ

@[simp] theorem conjugationOp_apply {d : Nat} (Z v : Mat d) :
    conjugationOp Z (hsVector v)=hsVector (Z*v*Z) := rfl

theorem conjugationOp_square {d : Nat} (Z : Mat d) (hZ : IsInvolution Z) (v : HSSpace d) :
    conjugationOp Z (conjugationOp Z v)=v := by
  apply (hsVectorEquiv d).symm.injective
  change Z*(Z*hsMatrix v*Z)*Z=hsMatrix v
  calc
    _=(Z*Z)*hsMatrix v*(Z*Z) := by simp only [Matrix.mul_assoc]
    _=_ := by rw [hZ.2]; simp

theorem conjugationOp_norm {d : Nat} (Z : Mat d) (hZ : IsInvolution Z) (v : HSSpace d) :
    ‖conjugationOp Z v‖=‖v‖ := by
  change ‖hsVector (Z*hsMatrix v*Z)‖=‖v‖
  rw [hsVector_norm,hsNorm_unitary_right Z _ (by rw [hZ.1,hZ.2]),
    hsNorm_unitary_left Z _ (by rw [hZ.1,hZ.2]),hsMatrix_norm]

theorem conjugationOp_inner {d : Nat} (Z : Mat d) (hZ : IsInvolution Z) (v w : HSSpace d) :
    inner ℝ (conjugationOp Z v) (conjugationOp Z w)=inner ℝ v w := by
  have h := norm_add_sq_real (conjugationOp Z v) (conjugationOp Z w)
  rw [← map_add,conjugationOp_norm Z hZ,conjugationOp_norm Z hZ,conjugationOp_norm Z hZ] at h
  nlinarith [norm_add_sq_real v w]

def matrixReflection {d : Nat} (Z : Mat d) (hZ : IsInvolution Z) : Reflection (HSSpace d) where
  op := conjugationOp Z
  square := conjugationOp_square Z hZ
  selfAdjoint v w := by
    calc
      _=inner ℝ (conjugationOp Z v) (conjugationOp Z (conjugationOp Z w)) := by rw [conjugationOp_square Z hZ]
      _=_ := conjugationOp_inner Z hZ v (conjugationOp Z w)

theorem matrixReflection_error {d : Nat} (Z : Mat d) (hZ : IsInvolution Z) (v : Mat d) :
    ‖hsVector v-(matrixReflection Z hZ).op (hsVector v)‖=hsNorm (comm Z v) := by
  change ‖hsVector v-hsVector (Z*v*Z)‖=hsNorm (comm Z v)
  rw [← hsVector_sub,hsVector_norm]
  have he : v-Z*v*Z= -(comm Z v)*Z := by
    simp only [comm,Matrix.neg_mul,Matrix.sub_mul,Matrix.mul_assoc, hZ.2,Matrix.mul_one]
    abel
  rw [he,hsNorm_unitary_right Z _ (by rw [hZ.1,hZ.2]),hsNorm_eq_frobenius,
    norm_neg,← hsNorm_eq_frobenius]

theorem matrixReflection_neg_error {d : Nat} (Z : Mat d) (hZ : IsInvolution Z) (v : Mat d) :
    ‖hsVector v-(matrixReflection Z hZ).neg.op (hsVector v)‖=hsNorm (anti Z v) := by
  change ‖hsVector v-(-hsVector (Z*v*Z))‖=hsNorm (anti Z v)
  rw [sub_neg_eq_add,← hsVector_add,hsVector_norm]
  have he : v+Z*v*Z=(anti Z v)*Z := by
    simp only [anti,Matrix.add_mul,Matrix.mul_assoc,hZ.2,Matrix.mul_one]
    abel
  rw [he,hsNorm_unitary_right Z _ (by rw [hZ.1,hZ.2])]

structure SignedInvolution (d : Nat) where
  matrix : Mat d
  involution : IsInvolution matrix
  negative : Bool

def SignedInvolution.reflection {d : Nat} (z : SignedInvolution d) : Reflection (HSSpace d) :=
  if z.negative then (matrixReflection z.matrix z.involution).neg else matrixReflection z.matrix z.involution

def SignedInvolution.error {d : Nat} (z : SignedInvolution d) (v : Mat d) : ℝ :=
  hsNorm (if z.negative then anti z.matrix v else comm z.matrix v)

theorem SignedInvolution.reflection_error {d : Nat} (z : SignedInvolution d) (v : Mat d) :
    ‖hsVector v-z.reflection.op (hsVector v)‖=z.error v := by
  unfold SignedInvolution.reflection SignedInvolution.error
  split
  · exact matrixReflection_neg_error z.matrix z.involution v
  · exact matrixReflection_error z.matrix z.involution v

@[reducible] def reflectionList {d : Nat} : List (SignedInvolution d) → List (Reflection (HSSpace d))
  | [] => []
  | z::zs => z.reflection::reflectionList zs

theorem reflectionList_length {d : Nat} (zs : List (SignedInvolution d)) :
    (reflectionList zs).length=zs.length := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [reflectionList,List.length_cons,ih]

theorem reflectionList_map {d : Nat} {A : Type*} (zs : List (SignedInvolution d))
    (f : Reflection (HSSpace d) → A) :
    (reflectionList zs).map f=zs.map (fun z => f z.reflection) := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [reflectionList,List.map_cons,ih]

/-- Explicit signed conjugations on matrices, using the Boolean word in
the listed reflections. `matrixReflection` is the actual operation v ↦ ZvZ. -/
def matrixTwirlWord {d : Nat} (zs : List (SignedInvolution d))
    (g : Fin (reflectionList zs).length → Bool) (v : Mat d) : Mat d :=
  hsMatrix (reflectionWord (reflectionList zs) g (hsVector v))

theorem matrixTwirlWord_nil {d : Nat} (g : Fin 0 → Bool) (v : Mat d) :
    matrixTwirlWord [] g v=v := rfl

theorem matrixTwirlWord_cons {d : Nat} (z : SignedInvolution d) (zs : List (SignedInvolution d))
    (g : Fin ((reflectionList zs).length+1) → Bool) (v : Mat d) :
    matrixTwirlWord (z::zs) g v=matrixTwirlWord zs (Fin.tail g)
      (if g 0 then (if z.negative then -(z.matrix*v*z.matrix) else z.matrix*v*z.matrix) else v) := by
  cases hg : g 0 <;> cases hz : z.negative <;>
    simp [matrixTwirlWord,reflectionList,reflectionWord,SignedInvolution.reflection,hg,hz,Reflection.neg,
      hsVector_neg,matrixReflection,conjugationOp_apply]

def twirlConjugator {d : Nat} : (zs : List (SignedInvolution d)) →
    (Fin (reflectionList zs).length → Bool) → Mat d
  | [],_ => 1
  | z::zs,g => twirlConjugator zs (Fin.tail g)*(if g 0 then z.matrix else 1)

def twirlSign {d : Nat} : (zs : List (SignedInvolution d)) →
    (Fin (reflectionList zs).length → Bool) → ℂ
  | [],_ => 1
  | z::zs,g => twirlSign zs (Fin.tail g)*(if g 0 && z.negative then -1 else 1)

/-- The word is exactly the signed two-sided conjugation appearing in the
paper, including the reverse order on the left and the original order on
the right. This connects the Hilbert-space average to matrix multiplication. -/
theorem matrixTwirlWord_formula {d : Nat} (zs : List (SignedInvolution d))
    (g : Fin (reflectionList zs).length → Bool) (v : Mat d) :
    matrixTwirlWord zs g v=twirlSign zs g •
      (twirlConjugator zs g*v*(twirlConjugator zs g).conjTranspose) := by
  induction zs generalizing v with
  | nil => simp [matrixTwirlWord,reflectionList,reflectionWord,twirlSign,twirlConjugator]
  | cons z zs ih =>
    rw [matrixTwirlWord_cons,ih]
    cases hg : g 0 <;> cases hz : z.negative <;>
      simp [twirlSign,twirlConjugator,hg,hz,Matrix.conjTranspose_mul,z.involution.1,
        Matrix.mul_assoc,Matrix.mul_neg,Matrix.neg_mul,smul_neg,neg_smul]

/-- Lemma 3.8 / two-sided twirls, for actual complex matrices and the
unnormalized Hilbert--Schmidt norm. Both commutators and anticommutators are
included through the explicit sign of each listed involution. -/
theorem matrix_twirl_bound {d : Nat} (zs : List (SignedInvolution d)) (v : Mat d) :
    (∑ g : Fin (reflectionList zs).length → Bool,
      hsNorm (matrixTwirlWord zs g v-v)^2)/(2:ℝ)^zs.length≤
      (zs.map (fun z => (z.error v)^2)).sum := by
  have h := twirl_bound (reflectionList zs) (hsVector v)
  have hn (g : Fin (reflectionList zs).length → Bool) :
      hsNorm (matrixTwirlWord zs g v-v)=
        ‖reflectionWord (reflectionList zs) g (hsVector v)-hsVector v‖ := by
    rw [← hsMatrix_norm]
    rfl
  simp_rw [hn]
  simpa only [reflectionList_length,reflectionList_map,SignedInvolution.reflection_error] using h

end
end Companion.Analytic


