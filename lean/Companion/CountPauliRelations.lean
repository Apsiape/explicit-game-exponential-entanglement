import Companion.CountPauliEmbedding

namespace Companion.Analytic
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 400000

theorem cubeShift_right {M d : Nat} {δ : Type*} (i : Fin M)
    (A : Matrix δ ((Fin M → Bool) × Fin d) ℂ) (a : δ) (g : Fin M → Bool) (b : Fin d) :
    (A*cubeShift (d:=d) i) a (g,b)=A a (flip g i,b) := by
  rw [cubeShift,Equiv.Perm.permMatrix,PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem bitSign_flip {M : Nat} (g : Fin M → Bool) (i j : Fin M) :
    bitSign (flip g j) i=if i=j then -bitSign g i else bitSign g i := by
  by_cases h : i=j
  · subst j
    cases hg : g i <;> simp [bitSign,flip,hg]
  · simp [bitSign,flip,h]

theorem cubeTwist_hermitian {M d : Nat} (X : Mat d) (hX : X.IsHermitian) (i : Fin M) :
    (cubeTwist X i).conjTranspose=cubeTwist X i := by
  ext ⟨g,a⟩ ⟨h,b⟩
  have hx : star (X b a)=X a b := congrFun (congrFun hX.eq a) b
  by_cases he : g=h
  · subst h
    cases hg : g i <;> simp [Matrix.conjTranspose_apply,cubeTwist,bitSign,hg,hx]
  · simp [Matrix.conjTranspose_apply,cubeTwist,he,Ne.symm he]

theorem cubeTwist_square {M d : Nat} (X : Mat d) (hX : X*X=1) (i : Fin M) :
    cubeTwist X i*cubeTwist X i=1 := by
  ext ⟨g,a⟩ ⟨h,b⟩
  rw [cubeTwist_mul]
  have hx : (∑ c, X a c*X c b)=(1:Mat d) a b := congrFun (congrFun hX a) b
  by_cases he : g=h
  · subst h
    cases hg : g i <;> by_cases hab : a=b <;>
      simp [cubeTwist,bitSign,hg,hx,Matrix.one_apply,Prod.mk.injEq,hab] <;>
      simpa [hab,Matrix.one_apply] using hx
  · simp [cubeTwist,he,Ne.symm he,Matrix.one_apply,Prod.mk.injEq]

theorem cubeTwist_involution {M d : Nat} (X : Mat d) (hX : IsInvolution X) (i : Fin M) :
    (cubeTwist X i).conjTranspose=cubeTwist X i ∧ cubeTwist X i*cubeTwist X i=1 :=
  ⟨cubeTwist_hermitian X hX.1 i,cubeTwist_square X hX.2 i⟩

/-- Exact Pauli conjugation on the enlarged space: the shift flips only the
matching phase coordinate. This identity holds for every matrix X. -/
theorem cubeTwist_shift {M d : Nat} (X : Mat d) (i j : Fin M) :
    cubeTwist X i*cubeShift j=(if i=j then (-1:ℂ) else 1) • (cubeShift j*cubeTwist X i) := by
  ext ⟨g,a⟩ ⟨h,b⟩
  rw [cubeShift_right,Matrix.smul_apply,cubeShift_mul]
  have hm : g=flip h j ↔ flip g j=h := by
    constructor
    · intro he; rw [he,flip_flip]
    · intro he; rw [← he,flip_flip]
  by_cases he : g=flip h j
  · have he' := hm.mp he
    simp only [cubeTwist,if_pos he,if_pos he',smul_eq_mul]
    rw [bitSign_flip]
    by_cases hij : i=j <;> simp [hij]
  · have he' : flip g j≠h := fun hh => he (hm.mpr hh)
    simp only [cubeTwist,if_neg he,if_neg he',smul_eq_mul,mul_zero]

theorem cubeTwist_anticommute {M d : Nat} (X : Mat d) (i : Fin M) :
    cubeTwist X i*cubeShift i= -(cubeShift i*cubeTwist X i) := by
  simpa using cubeTwist_shift X i i

theorem cubeTwist_commute {M d : Nat} (X : Mat d) (i j : Fin M) (hij : i≠j) :
    Commute (cubeTwist X i) (cubeShift j) := by
  change cubeTwist X i*cubeShift j=cubeShift j*cubeTwist X i
  simpa [hij] using cubeTwist_shift X i j

end
end Companion.Analytic
