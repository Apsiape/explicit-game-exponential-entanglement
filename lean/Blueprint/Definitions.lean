import Companion.FlatReturn
import Companion.EntropyRank
import Companion.GeneralGadgetTheorem
import Companion.Derivations
import Companion.PresentationModel

namespace Blueprint
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder ENNReal
set_option maxHeartbeats 600000

def log2 (x : ℝ) : ℝ := Real.log x/Real.log 2
def bfun (e : ℝ) : ℝ := (2:ℝ)^(-4*(24+log2 (log2 (1/e)))^2)
def mainC : ℝ := 49/(10:ℝ)^35
def mainEps : ℝ := (2:ℝ)^(-5500:ℤ)
def mainUpperC : ℝ := 74000000000
def sourceC : ℝ := 1/41000000
def cPsi : ℝ := 14826
def cStar : ℝ := 294240*Real.sqrt 5061*cPsi
def rank {d : Nat} (rho : Mat d) : Nat := Module.finrank ℂ (LinearMap.range (Matrix.toLin' rho))
def mainRate (eps : ℝ) : ℝ := mainC/eps*bfun eps

def sourceModel {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ) : Prop :=
  (∀ j, IsUnitary (U j)) ∧
  (∀ r∈pauliRelators, hs ((wordEval U r-1)*s.xi)≤e) ∧
  (∀ j, 1≤j → j≤6 → hs (comm (U j) s.xi)≤e)

def lampJ : Word := [(5,true),(6,true),(5,true),(6,true)]
def presentationModel {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ) : Prop :=
  (∀ j, IsUnitary (U j)) ∧
  (∀ k r, presentationRelator inputPresentation k=some r → hs ((wordEval U r-1)*s.xi)≤e) ∧
  (∀ j : Nat, 1 ≤ j → j ≤ inputPresentation.n0+1 → hs (comm (U j) s.xi)≤e)

def normalizedRepresentation {d : Nat} (R : List Word) (U : Nat → Mat d) (e : ℝ) : Prop :=
  (∀ j, IsUnitary (U j)) ∧ ∀ r∈R, normalizedHS (wordEval U r-1)≤e

def maximalEntanglementProfile (g : LCS) (eps : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ d : Nat, ∃ s : Strategy g d d,
    s.psi=(((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • (1:Mat d) ∧ 1-eps≤win s ∧ v=(d:ℝ≥0∞)}

def profileExponent (f : ℝ → ℝ≥0∞) : Prop :=
  Filter.Tendsto (fun eps => Real.log (log2 ((f eps).toReal))/Real.log (1/eps))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

def pureDensity {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun i j => psi i.2 i.1*star (psi j.2 j.1)

def decomposition {a b N : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Fin N → ℝ) (psi : Fin N → Matrix (Fin b) (Fin a) ℂ) : Prop :=
  (∀ j, 0≤p j) ∧ (∑ j, p j)=1 ∧ (∀ j, hs (psi j)=1) ∧
    sigma.matrix=∑ j, (p j:ℂ) • pureDensity (psi j)

/-- Finite-ensemble convex roof in bits; existence/equivalence obligations
are explicit lemmas in MixedStates.lean. -/
def finiteFormation {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) : ℝ :=
  sInf {v | ∃ N p psi, decomposition (N:=N) sigma p psi ∧
    v=∑ j, p j*entropy ((psi j).conjTranspose*psi j)}

def countableDecomposition {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (psi : Nat → Matrix (Fin b) (Fin a) ℂ) : Prop :=
  (∀ j, 0≤p j) ∧ HasSum p 1 ∧ (∀ j, hs (psi j)=1) ∧
    HasSum (fun j => (p j:ℂ) • pureDensity (psi j)) sigma.matrix

/-- Ordinary countable-ensemble convex roof, in bits. -/
def entanglementFormation {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) : ℝ :=
  sInf {v | ∃ p psi, countableDecomposition sigma p psi ∧
    v=∑' j, p j*entropy ((psi j).conjTranspose*psi j)}

abbrev Measurements (g : LCS) (a b : Nat) :=
  (Fin g.system.equations.length → (Fin g.system.n → Bool) → Mat a) ×
    (Fin g.system.n → Bool → Mat b)

def validMeasurements {g : LCS} {a b : Nat} (m : Measurements g a b) : Prop :=
  (∀ i x, (m.1 i x).PosSemidef) ∧ (∀ i, ∑ x, m.1 i x=1) ∧
  (∀ i x, ¬validAnswer g i x → m.1 i x=0) ∧
  (∀ j c, (m.2 j c).PosSemidef) ∧ (∀ j, m.2 j true+m.2 j false=1)

def mixedWin {g : LCS} {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (m : Measurements g a b) : ℝ :=
  ∑ i, ∑ j, g.pi i j * if j.val∈(g.system.equations[i.val]).vars then
    ∑ x, (Matrix.trace (sigma.matrix*Matrix.kronecker (m.1 i x) (m.2 j (x j)))).re else 1

def MainPureLower : Prop := ∀ a b (s : Strategy MainProof.concreteLCS a b) eps,
  0<eps → eps≤mainEps → 1-eps≤win s →
  mainRate eps≤entropy (s.psi*s.psi.conjTranspose) ∧
    entropy (s.psi*s.psi.conjTranspose)≤log2 (rank (s.psi*s.psi.conjTranspose):ℝ)

def MainMixedLower : Prop := ∀ a b (sigma : QIT.State (Fin a × Fin b))
  (m : Measurements MainProof.concreteLCS a b) eps,
  validMeasurements m → 0<eps → eps≤mainEps/2 → 1-eps≤mixedWin sigma m →
    mainRate eps/4≤entanglementFormation sigma

def MainUpper : Prop := ∀ eps : ℝ, 0<eps → eps≤1/2 →
  maximalEntanglementProfile MainProof.concreteLCS eps≤
    ENNReal.ofReal (Real.exp (mainUpperC/eps*log2 (1/eps)))

end
end Blueprint
