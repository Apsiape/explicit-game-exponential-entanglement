import Blueprint.Definitions

namespace Blueprint
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

def contraction {d : Nat} (A : Mat d) : Prop := A.IsHermitian ∧ ‖A‖≤1
def chshPair {a b n : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) (i j : Fin n) : ℝ :=
  expectation psi (A i) (B i j+B j i)+expectation psi (A j) (B i j-B j i)
def chshBias {a b n : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) : ℝ :=
  (∑ i, ∑ j, if i<j then chshPair psi A B i j else 0)/(2*(n:ℝ)*(n-1:Nat))
def validCHSH {a b n : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) : Prop :=
  hs psi=1 ∧ (∀ i, contraction (A i)) ∧ (∀ i j, i≠j → contraction (B i j))
def optimalBias : ℝ := Real.sqrt 2/2
def chshM (n : Nat) (eps : ℝ) : Nat := ⌊min (n:ℝ) ((1/10000000:ℝ)/eps)/3⌋₊
def chshEntropyProfile (n : Nat) (eps : ℝ) : ℝ :=
  sInf {v | ∃ a b psi A B, validCHSH (n:=n) (a:=a) (b:=b) psi A B ∧
    (1-eps)*optimalBias≤chshBias psi A B ∧ v=entropy (psi.conjTranspose*psi)}
def mixedCHSHBias {a b n : Nat} (sigma : QIT.State (Fin a × Fin b))
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) : ℝ :=
  (∑ i, ∑ j, if i<j then
    (sigma.matrix*(Matrix.kronecker (A i) (B i j+B j i)+Matrix.kronecker (A j) (B i j-B j i))).trace.re
    else 0)/(2*(n:ℝ)*(n-1:Nat))
def ELower : Prop := ∀ n a b psi A B eps,
  3≤n → 0<eps → validCHSH (n:=n) (a:=a) (b:=b) psi A B →
    (1-eps)*optimalBias≤chshBias psi A B →
    (chshM n eps:ℝ)/2≤entropy (psi.conjTranspose*psi) ∧
    (1/60000000:ℝ)*min (n:ℝ) (1/eps)-1/2≤entropy (psi.conjTranspose*psi)
def EProfiles : Prop := ∀ (n : Nat) (eps : ℝ), 3≤n → 0<eps → eps≤1 →
  (1/60000000:ℝ)*min (n:ℝ) (1/eps)-1/2≤chshEntropyProfile n eps ∧
  chshEntropyProfile n eps≤min ((n/2:Nat):ℝ) (⌈1/eps⌉₊:ℝ)
def EMixed : Prop := ∀ n a b (sigma : QIT.State (Fin a × Fin b)) A B eps,
  3≤n → 0<eps → (∀ i, contraction (A i)) →
    (∀ i j, i≠j → contraction (B i j)) →
    (1-eps)*optimalBias≤mixedCHSHBias (n:=n) sigma A B →
    (chshM n (2*eps):ℝ)/4≤entanglementFormation sigma

def kRelators : List Word := [
  [(4,true),(5,true),(4,false),(5,false),(5,false)],
  [(4,true),(3,true),(4,false),(3,false)],
  [(5,true),(1,true),(5,false),(2,false)],
  [(5,true),(2,true),(5,false),(1,false)],
  [(3,false),(1,true),(2,true)],[(1,true),(1,true)],[(2,true),(2,true)],[(3,true),(3,true)]]
def kModel {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ) : Prop :=
  (∀ j, IsUnitary (U j)) ∧ (∀ r∈kRelators, hs ((wordEval U r-1)*s.xi)≤e) ∧
   (∀ j, 1≤j → j≤5 → hs (comm (U j) s.xi)≤e) ∧ hs ((U 3+1)*s.xi)≤e
def kStateProfile (e : ℝ) : ℝ≥0∞ := sInf {v | ∃ (d : Nat) (U : Nat → Mat d) (s : State d), kModel U s e ∧ v=(d:ℝ≥0∞)}
def kHyperlinearProfile (delta e : ℝ) : ℝ≥0∞ := sInf {v | ∃ d U,
  0<d ∧ normalizedRepresentation (d:=d) kRelators U e ∧ delta≤normalizedHS (U 3-1) ∧ v=(d:ℝ≥0∞)}
def KProfile : Prop :=
  (∀ e : ℝ, 0<e → ENNReal.ofReal (1/(29*e))≤kStateProfile e ∧
    kStateProfile e≤kHyperlinearProfile 2 e ∧
    kHyperlinearProfile 2 e≤(2*⌈Real.pi/(Real.sqrt 2*e)⌉₊:Nat)) ∧
  (∀ delta : ℝ, 0<delta → delta≤2 → ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ e,
    0<e → e≤2 → ENNReal.ofReal (c/e)≤kHyperlinearProfile delta e ∧
      kHyperlinearProfile delta e≤ENNReal.ofReal (C/e))

end
end Blueprint
