import Companion.Kernel
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace Companion
namespace Analytic
noncomputable section
open scoped BigOperators ComplexOrder

abbrev Mat (d : Nat) := Matrix (Fin d) (Fin d) ℂ

/-- Unnormalized Hilbert--Schmidt norm, including rectangular matrices. -/
def hs {m n : Nat} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j))

def comm {d : Nat} (A B : Mat d) : Mat d := A*B-B*A
def anti {d : Nat} (A B : Mat d) : Mat d := A*B+B*A
def IsInvolution {d : Nat} (A : Mat d) : Prop := A.conjTranspose=A ∧ A*A=1
def IsUnitary {d : Nat} (A : Mat d) : Prop := A.conjTranspose*A=1 ∧ A*A.conjTranspose=1

/-- Spectral entropy in bits. The fallback only totalizes the definition;
every use below concerns a positive semidefinite matrix. `log 0 = 0`. -/
def entropy {d : Nat} (A : Mat d) : ℝ :=
  if h : A.IsHermitian then
    (∑ i, Real.negMulLog (h.eigenvalues i)) / Real.log 2
  else 0

def binaryEntropy (x : ℝ) : ℝ := Real.binEntropy x / Real.log 2

/-- The positive square root is supplied with its defining equations.
These are data constraints, not assumed analytic theorems. -/
structure State (d : Nat) where
  rho : Mat d
  positive : rho.PosSemidef
  normalized : Matrix.trace rho = 1
  xi : Mat d
  xi_positive : xi.PosSemidef
  xi_square : xi*xi=rho

def orderedZ {M d : Nat} (Z : Fin M → Mat d) (g : Fin M → Bool) : Mat d :=
  (List.ofFn (fun i => if g i then Z i else 1)).prod

def flip {M : Nat} (g : Fin M → Bool) (i : Fin M) : Fin M → Bool :=
  Function.update g i (!g i)

def aSquared {M d : Nat} (Z : Fin M → Mat d) (s : State d) (i : Fin M) : ℝ :=
  (∑ g : Fin M → Bool,
    (hs ((orderedZ Z (flip g i) - orderedZ Z g * Z i)*s.xi))^2) / (2:ℝ)^M

def bSquared {M d : Nat} (X Z : Fin M → Mat d) (s : State d) (i : Fin M) : ℝ :=
  (∑ g : Fin M → Bool,
    (hs (((if g i then (-1:ℂ) else 1) • (X i * orderedZ Z g) - orderedZ Z g * X i)*s.xi))^2) /
    (2:ℝ)^M

/-- Theorem 4.1, all three parts, in finite dimensions. -/
def Count : Prop := ∀ (M d : Nat) (X Z : Fin M → Mat d) (s : State d),
  (∀ i, IsInvolution (X i)) → (∀ i, IsInvolution (Z i)) →
  (∀ i, aSquared Z s i ≤
    2*(∑ j ∈ Finset.univ.filter (fun j => i<j),
      (hs (comm (Z i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2) +
    2*(∑ j ∈ Finset.univ.filter (fun j => i<j), (hs (comm (Z j) s.xi))^2)) ∧
  (∀ i, bSquared X Z s i ≤
    2*(hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi))^2 +
    2*(∑ j ∈ Finset.univ.filter (fun j => j≠i),
      (hs (comm (X i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2) +
    2*(∑ j, (hs (comm (Z j) s.xi))^2)) ∧
  (∑ i, (1 - (Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2/(2*Real.log 2) -
    binaryEntropy (min ((Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4) (1/2)))) ≤
      entropy s.rho

/-- Theorem C / Corollary 4.2, with every operator hypothesis explicit. -/
def UniformCount : Prop := ∀ (M d : Nat) (X Z : Fin M → Mat d) (s : State d) (kappa : ℝ),
  2≤M → (∀ i, IsInvolution (X i)) → (∀ i, IsInvolution (Z i)) →
  (∀ i j, i≠j → hs (comm (Z i) (Z j)*s.xi)≤kappa) →
  (∀ i j, i≠j → hs (comm (X i) (Z j)*s.xi)≤kappa) →
  (∀ i, hs (anti (X i) (Z i)*s.xi)≤kappa) →
  (∀ i, hs (comm (X i) s.xi)≤kappa) → (∀ i, hs (comm (Z i) s.xi)≤kappa) →
  16*(M:ℝ)*kappa^2≤1/10 →
    (3/4:ℝ)*M≤entropy s.rho ∧
    (2:ℝ)^((3/4:ℝ)*M)≤(Module.finrank ℂ (LinearMap.range (Matrix.toLin' s.rho)):ℝ)

structure LCS where
  system : Game
  rows_nonempty : ∀ e ∈ system.equations, e.vars ≠ []
  rows_nodup : ∀ e ∈ system.equations, e.vars.Nodup
  rows_sorted : ∀ e ∈ system.equations, e.vars.Pairwise (· < ·)
  rows_bounded : ∀ e ∈ system.equations, ∀ j ∈ e.vars, j < system.n
  rows_exist : system.equations ≠ []
  pi : Fin system.equations.length → Fin system.n → ℝ
  pi_nonneg : ∀ i j, 0≤pi i j
  pi_normalized : ∑ i, ∑ j, pi i j = 1
  piMin : ℝ
  piMin_pos : 0<piMin
  piMin_lower : ∀ i j, j.val ∈ (system.equations[i.val]).vars → piMin≤pi i j
  piMin_attained : ∃ i j, j.val ∈ (system.equations[i.val]).vars ∧ pi i j=piMin
  arity : Nat
  arity_upper : ∀ e ∈ system.equations, e.vars.length≤arity
  arity_attained : ∃ e ∈ system.equations, e.vars.length=arity

def answerBit (g : LCS) (a : Fin g.system.n → Bool) (j : Nat) : Bool :=
  if h : j<g.system.n then a ⟨j,h⟩ else false

def validAnswer (g : LCS) (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) : Prop :=
  ((g.system.equations[i.val]).vars.map (answerBit g a)).foldl Bool.xor false =
    (g.system.equations[i.val]).rhs

structure Strategy (g : LCS) (dA dB : Nat) where
  psi : Matrix (Fin dB) (Fin dA) ℂ
  normalized : hs psi=1
  alice : Fin g.system.equations.length → (Fin g.system.n → Bool) → Mat dA
  alice_positive : ∀ i a, (alice i a).PosSemidef
  alice_complete : ∀ i, ∑ a, alice i a = 1
  alice_valid : ∀ i a, ¬validAnswer g i a → alice i a = 0
  bob : Fin g.system.n → Bool → Mat dB
  bob_positive : ∀ j b, (bob j b).PosSemidef
  bob_complete : ∀ j, bob j true+bob j false=1

def expectation {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ) (P : Mat dA) (Q : Mat dB) : ℝ :=
  (∑ b, ∑ a, star (psi b a) * ((Q*psi)*P.transpose) b a).re

def pairWin {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) : ℝ :=
  if j.val ∈ (g.system.equations[i.val]).vars then
    ∑ a, expectation s.psi (s.alice i a) (s.bob j (a j))
  else 1

def win {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) : ℝ :=
  ∑ i, ∑ j, g.pi i j * pairWin s i j

def wordEval {d : Nat} (U : Nat → Mat d) (w : Word) : Mat d :=
  (w.map (fun a => if a.2 then U a.1 else (U a.1).conjTranspose)).prod

structure Model (g : LCS) (d : Nat) (e : ℝ) where
  state : State d
  U : Nat → Mat d
  unitary : ∀ j, IsUnitary (U j)
  relators : ∀ k r, relator g.system k = some r → hs ((wordEval U r-1)*state.xi)≤e
  state_commutators : ∀ j, 1≤j → j≤g.system.n+1 → hs (comm (U j) state.xi)≤e
  central_visible : hs ((U (g.system.n+1)+1)*state.xi)≤e

def theta (g : LCS) (eps : ℝ) : ℝ := 2*Real.sqrt (eps/g.piMin)
def transferPrecision (g : LCS) (eps : ℝ) : ℝ := max (g.arity:ℝ) 4 * theta g eps

/-- Finite-dimensional transfer, including compression to exactly the Schmidt
support, full rank, exact `J=-I`, and retention of Bob's reduced state. -/
def Transfer : Prop := ∀ (g : LCS) (dA dB : Nat) (s : Strategy g dA dB) (eps : ℝ),
  0≤eps → 1-eps≤win s →
  ∃ (r : Nat) (model : Model g r (transferPrecision g eps)),
    0<r ∧ r≤dA ∧ r≤dB ∧ model.state.rho.PosDef ∧
    model.U (g.system.n+1) = -1 ∧
    (∀ j, 1≤j → j≤g.system.n → IsInvolution (model.U j)) ∧
    (∀ j, 1≤j → j≤g.system.n → hs (comm (model.U j) model.state.xi)≤Real.sqrt 2*theta g eps) ∧
    ∃ V : Matrix (Fin dB) (Fin r) ℂ,
      V.conjTranspose*V=1 ∧ V*model.state.rho*V.conjTranspose=s.psi*s.psi.conjTranspose

def nu (l : Nat) : ℝ :=
  3*(1+((l:ℝ)-1)*((l:ℝ)-2)/2)+13*((l:ℝ)-1)/Real.sqrt 2
def returnConstant (s : Nat) : ℝ :=
  ((nu s)^2+((s:ℝ)^2+2+∑ l ∈ Finset.range s, nu (l+1))^2)/4

/-- The existence conclusion of the finite-dimensional return theorem.
The paper additionally specifies the sequential measurement realizing it. -/
def ReturnExistence : Prop := ∀ (g : LCS) (d : Nat) (e : ℝ) (model : Model g d e),
  0<e → ∃ s : Strategy g d d, s.psi=model.state.xi ∧
    ∀ i j, j.val ∈ (g.system.equations[i.val]).vars →
      1-pairWin s i j≤returnConstant g.arity*e^2

end
end Analytic
end Companion
