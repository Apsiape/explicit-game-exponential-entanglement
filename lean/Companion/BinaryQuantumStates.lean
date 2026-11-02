import Companion.EntropyIsometry
import Companion.BinaryHellinger

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

def krausChannel {a b k : Type*} [Fintype a] [Fintype b] [Fintype k] [DecidableEq a] [DecidableEq b]
    (K : k → Matrix b a ℂ) (hK : ∑ i, (K i).conjTranspose*K i=1) : QIT.Channel a b where
  map := QIT.MatrixMap.ofKraus K
  completelyPositive := QIT.MatrixMap.ofKraus_completelyPositive K
  tracePreserving := QIT.MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one K
    (by simpa only [QIT.MatrixMap.krausAdjoint,Matrix.mul_one] using hK)
  mapsPositive := QIT.MatrixMap.ofKraus_mapsPositive K

def unitProductEquiv (a : Type*) : a ≃ PUnit.{1} × a where
  toFun x := (PUnit.unit,x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by cases x with | mk u x => cases u; rfl

/-- Local port of QuAIR's pure-state entropy proof from
QIT/Information/AlickiFannesWinter.lean (Apache-2.0, QuAIR Team,
commit 8a931d4bda61ba503cfc0728704cfef5dedf2cff). Only the already checked
marginal-entropy identity is used; no additional upstream module is imported. -/
theorem pure_entropy_zero {a : Type*} [Fintype a] [DecidableEq a] (psi : QIT.PureVector a) :
    psi.state.vonNeumann=0 := by
  let phi := psi.reindex (unitProductEquiv a)
  have hA : phi.state.marginalA.vonNeumann=0 := QIT.State.vonNeumann_punit_eq_zero _
  have hB : phi.state.marginalB=psi.state := by
    apply QIT.State.ext
    ext i j
    simp [phi,QIT.State.marginalB,unitProductEquiv,QIT.partialTraceA]
  have h := QIT.State.pureVector_marginalA_vonNeumann_eq_marginalB phi
  rw [hA,hB] at h
  exact h.symm

def binaryProbability (p : ℝ) (b : Bool) : ℝ := if b then 1-p else p
def binaryAmplitude (p : ℝ) (neg b : Bool) : ℂ :=
  if b then (if neg then -(Real.sqrt (1-p):ℂ) else (Real.sqrt (1-p):ℂ)) else (Real.sqrt p:ℂ)

theorem binaryAmplitude_square (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (neg b : Bool) :
    binaryAmplitude p neg b*star (binaryAmplitude p neg b)=(binaryProbability p b:ℂ) := by
  cases b <;> cases neg <;>
    simp [binaryAmplitude,binaryProbability,Complex.star_def,← Complex.ofReal_mul] <;>
    norm_cast <;> nlinarith [Real.sq_sqrt hp0,Real.sq_sqrt (show 0≤1-p by linarith)]

def binaryPure (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (neg : Bool) : QIT.PureVector Bool where
  amp := binaryAmplitude p neg
  trace_rankOne_eq_one := by
    simp only [QIT.rankOneMatrix_trace,dotProduct,Fintype.sum_bool,binaryAmplitude_square p hp0 hp1]
    simp [binaryProbability]

def binaryDiagonal (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) : QIT.State Bool where
  matrix := Matrix.diagonal (fun b => (binaryProbability p b:ℂ))
  pos := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro b
    cases b with
    | false => change (0:ℂ)≤(p:ℂ); exact_mod_cast hp0
    | true => change (0:ℂ)≤((1-p:ℝ):ℂ); exact_mod_cast (sub_nonneg.mpr hp1)
  trace_eq_one := by simp [Matrix.trace,binaryProbability,Fintype.sum_bool]

theorem binaryPure_diagonal (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (neg b : Bool) :
    (binaryPure p hp0 hp1 neg).state.matrix b b=(binaryProbability p b:ℂ) := by
  exact binaryAmplitude_square p hp0 hp1 neg b

theorem binary_midpoint (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (1/2:ℂ) • ((binaryPure p hp0 hp1 false).state.matrix+(binaryPure p hp0 hp1 true).state.matrix)=
      (binaryDiagonal p hp0 hp1).matrix := by
  ext a b
  by_cases h : a=b
  · subst b
    simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]
    rw [binaryPure_diagonal,binaryPure_diagonal]
    simp only [binaryDiagonal,Matrix.diagonal_apply_eq]
    ring
  · cases a <;> cases b <;>
      simp_all [binaryPure,QIT.PureVector.state,QIT.rankOneMatrix_apply,binaryAmplitude,binaryDiagonal,
        Matrix.diagonal,Complex.star_def] <;> ring

theorem binaryDiagonal_posDef (p : ℝ) (hp0 : 0<p) (hp1 : p<1) :
    (binaryDiagonal p hp0.le hp1.le).matrix.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro b
  cases b with
  | false => change (0:ℂ)<(p:ℂ); exact_mod_cast hp0
  | true => change (0:ℂ)<((1-p:ℝ):ℂ); exact_mod_cast (sub_pos.mpr hp1)

theorem binary_relativeEntropy (p : ℝ) (hp0 : 0<p) (hp1 : p<1) (neg : Bool) :
    (binaryPure p hp0.le hp1.le neg).state.relativeEntropy (binaryDiagonal p hp0.le hp1.le)=
      (binaryEntropy p:EReal) := by
  let rho := (binaryPure p hp0.le hp1.le neg).state
  let sigma := binaryDiagonal p hp0.le hp1.le
  have hpd : sigma.matrix.PosDef := binaryDiagonal_posDef p hp0 hp1
  have hs : QIT.Matrix.Supports rho.matrix sigma.matrix := QIT.Matrix.Supports.of_right_posDef _ _ hpd
  change rho.relativeEntropy sigma=_
  rw [QIT.State.relativeEntropy_eq_coe_of_supports rho sigma hs,
    QIT.State.relativeEntropyPSDReferenceTraceLogFinite_eq_posDef_formula rho hpd hs]
  have hr : rho.vonNeumann=0 := pure_entropy_zero _
  rw [hr]
  have hl : QIT.State.psdLog sigma.matrix hpd=
      Matrix.diagonal (fun b => (Real.log (binaryProbability p b):ℂ)) := by
    rw [QIT.State.psdLog]
    exact QIT.cfc_diagonal_ofReal (binaryProbability p) Real.log
  rw [hl]
  have ht : ((rho.matrix*Matrix.diagonal (fun b => (Real.log (binaryProbability p b):ℂ))).trace).re=
      p*Real.log p+(1-p)*Real.log (1-p) := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,Fintype.sum_bool,rho,
      binaryPure_diagonal,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    simp [binaryProbability]
    ring
  rw [ht]
  congr 1
  simp only [binaryEntropy,Real.binEntropy,Real.log_inv,neg_zero,zero_sub]
  ring

end
end Companion.Analytic.CountProof
