import Companion.Analytic
import Mathlib.Basic.ENNReal.Real

namespace Companion.Analytic
noncomputable section
open scoped BigOperators ENNReal

/-- Spectral nearest-involution rounding. The tie at real part zero is +1.
The fallback totalizes the definition; the Hermitian branch holds for every U. -/
def roundUnitary {d : Nat} (U : Mat d) : Mat d :=
  let H := (1/2:ℂ) • (U+U.conjTranspose)
  if h : H.IsHermitian then
    Unitary.conjStarAlgAut ℂ (Mat d) h.eigenvectorUnitary
      (Matrix.diagonal (fun i => if 0≤h.eigenvalues i then (1:ℂ) else -1))
  else 1

/-- False records the +1 sign and true records the -1 sign. -/
def signProjection {d : Nat} (B : Mat d) (a : Bool) : Mat d :=
  (1/2:ℂ) • (1 + if a then -B else B)

def sequentialKraus {d : Nat} (g : LCS) (B : Fin g.system.n → Mat d)
    (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) : Mat d :=
  (((g.system.equations[i.val]).vars.map fun j =>
    if h : j<g.system.n then signProjection (B ⟨j,h⟩).transpose (a ⟨j,h⟩) else 1).reverse).prod

def correctedAnswer (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin g.system.n → Bool) : Fin g.system.n → Bool := by
  classical
  exact if validAnswer g i a then a else
    fun j => if j.val=(g.system.equations[i.val]).vars.getLast?.getD 0 then !(a j) else a j

/-- The POVM effect for the sequential procedure followed by the deterministic
last-bit parity correction. Unasked coordinates are fixed to false, so every
physical branch occurs once in the full-assignment answer encoding. -/
def sequentialAlice {d : Nat} (g : LCS) (B : Fin g.system.n → Mat d)
    (i : Fin g.system.equations.length) (out : Fin g.system.n → Bool) : Mat d :=
  ∑ a : Fin g.system.n → Bool,
    if (∀ j, j.val ∉ (g.system.equations[i.val]).vars → a j=false) ∧
        correctedAnswer g i a=out then
      (sequentialKraus g B i a).conjTranspose*sequentialKraus g B i a
    else 0

/-- The full finite-dimensional return statement, including the specified
rounded Bob observables, Alice's sequential measurement, and the zero-error case.
This is a statement, not an assumed entropy or measurement theorem. -/
def Return : Prop := ∀ (g : LCS) (d : Nat) (e : ℝ) (model : Model g d e),
  0≤e → ∃ s : Strategy g d d,
    s.psi=model.state.xi ∧
    (∀ j b, s.bob j b=signProjection (roundUnitary (model.U (j.val+1))) b) ∧
    (∀ i a, s.alice i a=sequentialAlice g (fun j => roundUnitary (model.U (j.val+1))) i a) ∧
    (∀ i j, j.val ∈ (g.system.equations[i.val]).vars →
      1-pairWin s i j≤returnConstant g.arity*e^2)

def quantumValueOne (g : LCS) : Prop := ∀ eps : ℝ, 0<eps →
  ∃ (d : Nat) (s : Strategy g d d), 1-eps≤win s

/-- Extended nonnegative infima keep empty feasible sets at infinity. -/
def stateDimensionProfile (g : LCS) (e : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ d : Nat, Nonempty (Model g d e) ∧ v=(d:ℝ≥0∞)}
def gameDimensionProfile (g : LCS) (eps : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ (d : Nat) (s : Strategy g d d), 1-eps≤win s ∧ v=(d:ℝ≥0∞)}
def stateEntropyProfile (g : LCS) (e : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ (d : Nat) (m : Model g d e), v=ENNReal.ofReal (entropy m.state.rho)}
def gameEntropyProfile (g : LCS) (eps : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ (d : Nat) (s : Strategy g d d), 1-eps≤win s ∧
    v=ENNReal.ofReal (entropy (s.psi*s.psi.conjTranspose))}
def modelPrecisionProfile (g : LCS) (d : Nat) : ℝ≥0∞ :=
  sInf {v | ∃ (r : Nat) (e : ℝ), r≤d ∧ 0≤e ∧ Nonempty (Model g r e) ∧ v=ENNReal.ofReal e}
def gameLossProfile (g : LCS) (d : Nat) : ℝ≥0∞ :=
  sInf {v | ∃ s : Strategy g d d, v=ENNReal.ofReal (1-win s)}
def gameConstant (g : LCS) : ℝ := 2*max (g.arity:ℝ) 4/Real.sqrt g.piMin

/-- All three finite-dimensional profile conclusions of Corollary 5.5. -/
def TwoSided : Prop := ∀ g : LCS, quantumValueOne g →
  (∀ eps : ℝ, 0<eps →
    stateDimensionProfile g (gameConstant g*Real.sqrt eps)≤gameDimensionProfile g eps ∧
    gameDimensionProfile g eps≤stateDimensionProfile g (Real.sqrt (eps/returnConstant g.arity))) ∧
  (∀ eps : ℝ, 0<eps →
    stateEntropyProfile g (gameConstant g*Real.sqrt eps)≤gameEntropyProfile g eps ∧
    gameEntropyProfile g eps≤stateEntropyProfile g (Real.sqrt (eps/returnConstant g.arity))) ∧
  (∀ d : Nat,
    (modelPrecisionProfile g d)^2/(ENNReal.ofReal (gameConstant g))^2≤gameLossProfile g d ∧
    gameLossProfile g d≤ENNReal.ofReal (returnConstant g.arity)*(modelPrecisionProfile g d)^2)

end
end Companion.Analytic
