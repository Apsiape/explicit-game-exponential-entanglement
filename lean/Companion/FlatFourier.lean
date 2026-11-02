import Companion.CountOrderedProducts
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

def flatMatrix (n : Nat) [NeZero n] : Mat n := fun i j =>
  (uniformCoefficient (Fin n):ℂ)*ZMod.stdAddChar ((ZMod.finEquiv n i)*(ZMod.finEquiv n j))

theorem stdCharacter_pair (n : Nat) [NeZero n] (x a b : ZMod n) :
    star (ZMod.stdAddChar (x*a))*ZMod.stdAddChar (x*b)=ZMod.stdAddChar (x*(b-a)) := by
  rw [Complex.star_def,← AddChar.map_neg_eq_conj,← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem flatMatrix_isometry (n : Nat) [NeZero n] : (flatMatrix n).conjTranspose*flatMatrix n=1 := by
  ext a b
  let e := ZMod.finEquiv n
  let c : ℂ := uniformCoefficient (Fin n)
  have hc : c*c*(n:ℂ)=1 := by
    simpa only [Fintype.card_fin] using (show (uniformCoefficient (Fin n):ℂ)*
      (uniformCoefficient (Fin n):ℂ)*(Fintype.card (Fin n):ℂ)=1 by exact_mod_cast uniformCoefficient_square (Fin n))
  have ht (k : Fin n) : star (flatMatrix n k a)*flatMatrix n k b=
      c*c*ZMod.stdAddChar ((e k)*(e b-e a)) := by
    change star (c*ZMod.stdAddChar (e k*e a))*(c*ZMod.stdAddChar (e k*e b))=_
    calc
      _=c*c*(star (ZMod.stdAddChar (e k*e a))*ZMod.stdAddChar (e k*e b)) := by
        simp only [c,star_mul,Complex.star_def,Complex.conj_ofReal]
        ring
      _=_ := by rw [stdCharacter_pair]
  have he : (∑ k : Fin n, ZMod.stdAddChar ((e k)*(e b-e a)))=
      ∑ k : ZMod n, ZMod.stdAddChar (k*(e b-e a)) :=
    Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
  simp_rw [ht]
  rw [← Finset.mul_sum,he,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
  by_cases hab : a=b
  · subst b
    simpa [ZMod.card,Matrix.one_apply] using hc
  · have hdiff : e b-e a≠0 := sub_ne_zero.mpr (fun h => hab (e.injective h).symm)
    simp [hdiff,Matrix.one_apply,hab]

def flatUnitary (n : Nat) [NeZero n] : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨flatMatrix n,by
    change (flatMatrix n).conjTranspose*flatMatrix n=1 ∧ flatMatrix n*(flatMatrix n).conjTranspose=1
    exact ⟨flatMatrix_isometry n,mul_eq_one_comm.mp (flatMatrix_isometry n)⟩⟩

theorem flatMatrix_entry_square (n : Nat) [NeZero n] (i j : Fin n) :
    star (flatMatrix n i j)*flatMatrix n i j=
      (uniformCoefficient (Fin n):ℂ)*(uniformCoefficient (Fin n):ℂ) := by
  have h := stdCharacter_pair n (ZMod.finEquiv n i) (ZMod.finEquiv n j) (ZMod.finEquiv n j)
  have he : star (ZMod.stdAddChar (ZMod.finEquiv n i*ZMod.finEquiv n j))*
      ZMod.stdAddChar (ZMod.finEquiv n i*ZMod.finEquiv n j)=1 := by simpa using h
  unfold flatMatrix
  calc
    _=((uniformCoefficient (Fin n):ℂ)*(uniformCoefficient (Fin n):ℂ))*
        (star (ZMod.stdAddChar (ZMod.finEquiv n i*ZMod.finEquiv n j))*
          ZMod.stdAddChar (ZMod.finEquiv n i*ZMod.finEquiv n j)) := by
      simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
      ring
    _=_ := by rw [he,mul_one]

theorem flat_diagonal (n : Nat) [NeZero n] (v : Fin n → ℂ) (j : Fin n) :
    ((flatMatrix n).conjTranspose*Matrix.diagonal v*flatMatrix n) j j=
      ((uniformCoefficient (Fin n):ℂ)*(uniformCoefficient (Fin n):ℂ))*(∑ i, v i) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _=(star (flatMatrix n i j)*flatMatrix n i j)*v i := by ring
    _=_ := by rw [flatMatrix_entry_square]

end
end Companion.Analytic.CountProof
