import Companion.JointProjection

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem symmetryProjection_mul (C : Matrix a a ℂ) (hC : C*C=1) (s t : Bool) :
    symmetryProjection C s*symmetryProjection C t=if s=t then symmetryProjection C s else 0 := by
  cases s <;> cases t <;>
    simp only [symmetryProjection,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
      Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_neg,
      Matrix.neg_mul,Matrix.mul_one,Matrix.one_mul,hC] <;> module

/-- Distinct joint spectral outcomes are orthogonal. -/
theorem jointProjection_mul (n : Nat) (C : Fin n → Matrix a a ℂ)
    (hC : ∀ i, (C i).conjTranspose=C i ∧ C i*C i=1)
    (hc : ∀ i j, Commute (C i) (C j)) (g h : Fin n → Bool) :
    jointProjection n C g*jointProjection n C h=if g=h then jointProjection n C g else 0 := by
  induction n with
  | zero => simp [jointProjection,Subsingleton.elim g h]
  | succ n ih =>
    have hm := jointProjection_commute n (Fin.tail C) (symmetryProjection (C 0) (g 0))
      (fun i => (commute_symmetryProjection (C i.succ) (C 0) (hc i.succ 0) (g 0)).symm) (Fin.tail h)
    have he : jointProjection (n+1) C g*jointProjection (n+1) C h=
        (jointProjection n (Fin.tail C) (Fin.tail g)*jointProjection n (Fin.tail C) (Fin.tail h))*
          (symmetryProjection (C 0) (g 0)*symmetryProjection (C 0) (h 0)) := by
      rw [jointProjection,jointProjection]
      calc
        _=jointProjection n (Fin.tail C) (Fin.tail g)*
            (symmetryProjection (C 0) (g 0)*jointProjection n (Fin.tail C) (Fin.tail h))*
              symmetryProjection (C 0) (h 0) := by simp only [Matrix.mul_assoc]
        _=jointProjection n (Fin.tail C) (Fin.tail g)*
            (jointProjection n (Fin.tail C) (Fin.tail h)*symmetryProjection (C 0) (g 0))*
              symmetryProjection (C 0) (h 0) := by rw [hm.eq]
        _=_ := by simp only [Matrix.mul_assoc]
    rw [he,ih (Fin.tail C) (fun i => hC i.succ) (fun i j => hc i.succ j.succ),
      symmetryProjection_mul _ (hC 0).2]
    by_cases h0 : g 0=h 0
    · by_cases ht : Fin.tail g=Fin.tail h
      · have hh : g=h := by
          calc
            g=Fin.cons (g 0) (Fin.tail g) := (Fin.cons_self_tail g).symm
            _=Fin.cons (h 0) (Fin.tail h) := by rw [h0,ht]
            _=h := Fin.cons_self_tail h
        simp only [h0,ht,hh,↓reduceIte,jointProjection]
      · have hh : g≠h := fun e => ht (congrArg Fin.tail e)
        simp only [h0,ht,hh,↓reduceIte,Matrix.zero_mul]
    · have hh : g≠h := fun e => h0 (congrFun e 0)
      simp only [h0,hh,↓reduceIte,Matrix.mul_zero]

theorem jointProjection_square (n : Nat) (C : Fin n → Matrix a a ℂ)
    (hC : ∀ i, (C i).conjTranspose=C i ∧ C i*C i=1) (hc : ∀ i j, Commute (C i) (C j))
    (g : Fin n → Bool) : jointProjection n C g*jointProjection n C g=jointProjection n C g := by
  simpa only [↓reduceIte] using jointProjection_mul n C hC hc g g

end
end Companion.Analytic.CountProof
