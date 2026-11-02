import Blueprint.W2.EvenMatrices

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def evenRepresentation (m : Nat) (hm : 0<m) : Nat → Mat (2*m)
  | 1 => (halfSwap m hm).permMatrix ℂ
  | 2 => -(halfSwap m hm).permMatrix ℂ
  | 3 => -1
  | 4 => (shuffle m hm).permMatrix ℂ
  | 5 => evenClock m
  | _ => 1

theorem evenRepresentation_unitary (m : Nat) (hm : 0<m) (j : Nat) :
    IsUnitary (evenRepresentation m hm j) := by
  have hP := perm_unitary (halfSwap m hm)
  have hN : IsUnitary (-(halfSwap m hm).permMatrix ℂ) := by simpa [IsUnitary] using hP
  unfold evenRepresentation
  split
  · exact hP
  · exact hN
  · simp [IsUnitary]
  · exact perm_unitary _
  · exact evenClock_unitary m
  · simp [IsUnitary]

theorem evenRepresentation_first (m : Nat) (hm : 0<m) :
    normalizedHS (wordEval (evenRepresentation m hm) kRelators[0]-1)=
      Real.sqrt 2*Real.sin (Real.pi/(2*m)) := by
  have he := clock_shuffle_residual m hm
  rw [show kRelators[0]=[(4,true),(5,true),(4,false),(5,false),(5,false)] from rfl]
  simp only [wordEval,evenRepresentation,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,Bool.false_eq_true,↓reduceIte,Matrix.mul_one]
  have hnorm := congrArg normalizedHS he
  rw [even_residual_norm m hm] at hnorm
  simpa only [Matrix.mul_assoc] using hnorm

theorem evenRepresentation_exact (m : Nat) (hm : 0<m) :
    ∀ r∈kRelators.drop 1, wordEval (evenRepresentation m hm) r=1 := by
  let P := (halfSwap m hm).permMatrix ℂ
  let X := (shuffle m hm).permMatrix ℂ
  let Y := evenClock m
  have hP : IsUnitary P := perm_unitary _
  have hX : IsUnitary X := perm_unitary _
  have hY : IsUnitary Y := evenClock_unitary m
  have hP2 : P*P=1 := halfSwap_matrix_square m hm
  have hPstar : P.conjTranspose=P := by
    calc
      _=P.conjTranspose*(P*P) := by rw [hP2,Matrix.mul_one]
      _=P := by rw [←Matrix.mul_assoc,hP.1,Matrix.one_mul]
  have hYP : Y*P*Y.conjTranspose= -P :=
    flipped_conjugation P Y hP hY (clock_half_conjugation m hm)
  have hYN : Y*(-P)*Y.conjTranspose=P := by
    rw [Matrix.mul_neg,Matrix.neg_mul,hYP,neg_neg]
  have hXP : X*(-1)*X.conjTranspose*(-1:Mat (2*m)).conjTranspose=1 := by
    simp only [Matrix.conjTranspose_neg,Matrix.conjTranspose_one,Matrix.mul_neg,
      Matrix.neg_mul,Matrix.mul_one,neg_neg,hX.2]
  have hYA : Y*P*Y.conjTranspose*(-P).conjTranspose=1 := by
    rw [hYP,Matrix.conjTranspose_neg,Matrix.neg_mul,Matrix.mul_neg,neg_neg,hP.2]
  have hYB : Y*(-P)*Y.conjTranspose*P.conjTranspose=1 := by rw [hYN,hP.2]
  have hCAB : (-1:Mat (2*m)).conjTranspose*P*(-P)=1 := by
    simp only [Matrix.conjTranspose_neg,Matrix.conjTranspose_one,Matrix.neg_mul,
      Matrix.one_mul,Matrix.mul_neg,neg_neg,hP2]
  intro r hr
  simp only [kRelators,List.drop_succ_cons,List.drop_zero,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [wordEval,evenRepresentation,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,Bool.false_eq_true,↓reduceIte,Matrix.mul_one]
  · simpa only [P,X,Y,Matrix.mul_assoc] using hXP
  · simpa only [P,X,Y,Matrix.mul_assoc] using hYA
  · simpa only [P,X,Y,Matrix.mul_assoc] using hYB
  · simpa only [P,X,Y,Matrix.mul_assoc] using hCAB
  · exact hP2
  · simpa only [Matrix.neg_mul,Matrix.mul_neg,neg_neg] using hP2
  · simp

end
end Blueprint.W2
