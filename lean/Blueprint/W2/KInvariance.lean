import Blueprint.FCircle
import Blueprint.W2.KWords

namespace Blueprint.W2
noncomputable section
open Companion Companion.Analytic MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem k_near_global {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (hU : ∀ j, IsUnitary (U j))
    (hr : ∀ r∈kRelators, hs ((wordEval U r-1)*s.xi)≤e)
    (hc : ∀ j, hs (comm (U j) s.xi)≤e) (hvisible : hs ((U 3+1)*s.xi)≤e) :
    FCircle.W1 (Measure.map FCircle.doubling (FCircle.spectralMeasure (U 5) (hU 5) s))
      (FCircle.spectralMeasure (U 5) (hU 5) s)≤5*Real.pi*e ∧
    FCircle.W1 (Measure.map FCircle.halfTurn (FCircle.spectralMeasure (U 5) (hU 5) s))
      (FCircle.spectralMeasure (U 5) (hU 5) s)≤19/2*Real.pi*e := by
  let A := U 1
  let C := U 3
  let X := U 4
  let Y := U 5
  have hA : IsUnitary A := hU 1
  have hX : IsUnitary X := hU 4
  have hY : IsUnitary Y := hU 5
  have hC : IsUnitary C := hU 3
  have hI : IsUnitary (1:Mat d) := by simp [IsUnitary]
  have hNI : IsUnitary (-1:Mat d) := by simp [IsUnitary]
  have hAadj := ReturnProof.unitary_adjoint A hA
  have hword (r : Word) : hs (comm (wordEval U r) s.xi)≤r.length*e :=
    AWordArea.word_commutator U hU s.xi e hc r
  let P := Y*Y
  let Q := X*Y*X.conjTranspose
  have hP : IsUnitary P := ReturnProof.unitary_mul Y Y hY hY
  have hQ : IsUnitary Q := ReturnProof.unitary_mul _ _
    (ReturnProof.unitary_mul X Y hX hY) (ReturnProof.unitary_adjoint X hX)
  have hPc : hs (comm P s.xi)≤2*e := by
    simpa [P,Y,wordEval,Matrix.mul_assoc] using hword [(5,true),(5,true)]
  have hQc : hs (comm Q s.xi)≤3*e := by
    simpa [Q,X,Y,wordEval,Matrix.mul_assoc] using hword [(4,true),(5,true),(4,false)]
  let R := wordEval U kRelators[0]
  have hR := wordEval_unitary U hU kRelators[0]
  have hRe : hs ((R-1)*s.xi)≤e := hr _ (by simp [kRelators])
  have hRP : R*P=Q := kFirstWord_identity U hU
  have hQP : hs ((Q-P)*s.xi)≤5*e := by
    have h := ReturnProof.unitary_difference_right_transport R 1 P s.xi hR hI hP
    have hi : (R-1)*P=Q-P := by rw [Matrix.sub_mul,Matrix.one_mul,hRP]
    rw [hi] at h
    change hs ((Q-P)*s.xi)≤hs ((R-1)*s.xi)+2*hs (comm P s.xi) at h
    linarith
  have hPQ : hs (P*s.xi-s.xi*Q)≤8*e := by
    have h := hs_intertwiner_bound P Q s.xi
    linarith
  let mu := fun rho : State d => FCircle.spectralMeasure Y hY rho
  let tX := conjugatedState X hX s
  have hDouble : FCircle.W1 (Measure.map FCircle.doubling (mu s)) (mu s)≤5*Real.pi*e := by
    obtain ⟨_,_,_,_,_,hW⟩ := FCircle.coupling P Q hP hQ s
    rw [FCircle.spectral_square Y hY s,
      FCircle.spectral_conjugation X Y hX hY s tX rfl] at hW
    have hRot := FCircle.rotate_state X hX s tX rfl Y hY
    have hTri := FCircle.W1_triangle (Measure.map FCircle.doubling (mu s)) (mu tX) (mu s)
      (FCircle.map_probability FCircle.doubling FCircle.doubling_measurable (mu s)
        (FCircle.spectral_probability Y hY s))
      (FCircle.spectral_probability Y hY tX) (FCircle.spectral_probability Y hY s)
    calc
      _≤FCircle.W1 (Measure.map FCircle.doubling (mu s)) (mu tX)+FCircle.W1 (mu tX) (mu s) := hTri
      _≤Real.pi/2*(8*e)+Real.pi*e := add_le_add
        (hW.trans (mul_le_mul_of_nonneg_left hPQ (by positivity)))
        (hRot.trans (mul_le_mul_of_nonneg_left (hc 4) Real.pi_pos.le))
      _=_ := by ring
  let H := A.conjTranspose*Y*A
  let CY := C*Y
  have hCY : IsUnitary CY := ReturnProof.unitary_mul C Y hC hY
  have hH : IsUnitary H := ReturnProof.unitary_mul _ _
    (ReturnProof.unitary_mul _ _ hAadj hY) hA
  have hHc : hs (comm H s.xi)≤3*e := by
    simpa [H,A,Y,wordEval,Matrix.mul_assoc] using hword [(1,false),(5,true),(1,true)]
  have hCYc : hs (comm CY s.xi)≤2*e := by
    simpa [CY,C,Y,wordEval,Matrix.mul_assoc] using hword [(3,true),(5,true)]
  let Rhalf := wordEval U kHalfWord
  have hRhalf := wordEval_unitary U hU kHalfWord
  have hRhe : hs ((Rhalf-1)*s.xi)≤7*e := kHalfWord_defect U hU s.xi e hr hc
  have hRHCY : Rhalf*CY=H := kHalfWord_identity U hU
  have hHCY : hs ((H-CY)*s.xi)≤11*e := by
    have h := ReturnProof.unitary_difference_right_transport Rhalf 1 CY s.xi hRhalf hI hCY
    have hi : (Rhalf-1)*CY=H-CY := by rw [Matrix.sub_mul,Matrix.one_mul,hRHCY]
    rw [hi] at h
    change hs ((H-CY)*s.xi)≤hs ((Rhalf-1)*s.xi)+2*hs (comm CY s.xi) at h
    linarith
  have hCYplus : hs ((CY+Y)*s.xi)≤3*e := by
    have h := ReturnProof.unitary_difference_right_transport C (-1) Y s.xi hC hNI hY
    have hi : (C-(-1))*Y=CY+Y := by simp [CY,Matrix.add_mul]
    rw [hi,sub_neg_eq_add] at h
    change hs ((CY+Y)*s.xi)≤hs ((C+1)*s.xi)+2*hs (comm Y s.xi) at h
    linarith [hc 5]
  have hHY : hs ((H+Y)*s.xi)≤14*e := by
    have hi : (H+Y)*s.xi=(H-CY)*s.xi+(CY+Y)*s.xi := by
      simp only [Matrix.add_mul,Matrix.sub_mul]
      abel
    have h : hs ((H+Y)*s.xi)≤hs ((H-CY)*s.xi)+hs ((CY+Y)*s.xi) := by
      rw [hi,hs_eq_hsNorm]
      exact hsNorm_add_le _ _
    linarith
  have hNH : hs ((-Y)*s.xi-s.xi*H)≤17*e := by
    have h := hs_intertwiner_bound (-Y) H s.xi
    rw [sub_neg_eq_add] at h
    linarith
  have hNY : IsUnitary (-Y) := by
    simpa only [IsUnitary,Matrix.conjTranspose_neg,Matrix.neg_mul,Matrix.mul_neg,neg_neg] using hY
  let tA := conjugatedState A.conjTranspose hAadj s
  have hSpec : FCircle.spectralMeasure H hH s=mu tA := by
    have h := FCircle.spectral_conjugation A.conjTranspose Y hAadj hY s tA rfl
    simpa only [Matrix.conjTranspose_conjTranspose] using h
  have hHalf : FCircle.W1 (Measure.map FCircle.halfTurn (mu s)) (mu s)≤19/2*Real.pi*e := by
    obtain ⟨_,_,_,_,_,hW⟩ := FCircle.coupling (-Y) H hNY hH s
    rw [FCircle.spectral_negative Y hY s hNY,hSpec] at hW
    have hRot := FCircle.rotate_state A.conjTranspose hAadj s tA rfl Y hY
    rw [AWordArea.adjoint_commutator A s.xi hA] at hRot
    have hTri := FCircle.W1_triangle (Measure.map FCircle.halfTurn (mu s)) (mu tA) (mu s)
      (FCircle.map_probability FCircle.halfTurn FCircle.halfTurn_measurable (mu s)
        (FCircle.spectral_probability Y hY s))
      (FCircle.spectral_probability Y hY tA) (FCircle.spectral_probability Y hY s)
    calc
      _≤FCircle.W1 (Measure.map FCircle.halfTurn (mu s)) (mu tA)+FCircle.W1 (mu tA) (mu s) := hTri
      _≤Real.pi/2*(17*e)+Real.pi*e := add_le_add
        (hW.trans (mul_le_mul_of_nonneg_left hNH (by positivity)))
        (hRot.trans (mul_le_mul_of_nonneg_left (hc 1) Real.pi_pos.le))
      _=_ := by ring
  exact ⟨hDouble,hHalf⟩

end
end Blueprint.W2
