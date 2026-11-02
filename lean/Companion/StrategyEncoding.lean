import Companion.TensorEncoding

namespace Companion.Analytic
noncomputable section
open scoped BigOperators ComplexOrder

/-- The independent tensor-product presentation of a finite-dimensional
strategy. Local effects are matrices in the fixed local orthonormal bases. -/
structure TensorStrategy (g : LCS) (dA dB : Nat) where
  psi : JointSpace dA dB
  normalized : ‖psi‖=1
  alice : Fin g.system.equations.length → (Fin g.system.n → Bool) → Mat dA
  alice_positive : ∀ i a, (alice i a).PosSemidef
  alice_complete : ∀ i, ∑ a, alice i a=1
  alice_valid : ∀ i a, ¬validAnswer g i a → alice i a=0
  bob : Fin g.system.n → Bool → Mat dB
  bob_positive : ∀ j b, (bob j b).PosSemidef
  bob_complete : ∀ j, bob j true+bob j false=1

def TensorStrategy.toMatrix {g : LCS} {dA dB : Nat} (s : TensorStrategy g dA dB) : Strategy g dA dB where
  psi := thetaTensor s.psi
  normalized := by rw [thetaTensor_norm]; exact s.normalized
  alice := s.alice
  alice_positive := s.alice_positive
  alice_complete := s.alice_complete
  alice_valid := s.alice_valid
  bob := s.bob
  bob_positive := s.bob_positive
  bob_complete := s.bob_complete

def Strategy.toTensor {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) : TensorStrategy g dA dB where
  psi := thetaTensorInv s.psi
  normalized := by rw [← thetaTensor_norm,thetaTensor_right_inv]; exact s.normalized
  alice := s.alice
  alice_positive := s.alice_positive
  alice_complete := s.alice_complete
  alice_valid := s.alice_valid
  bob := s.bob
  bob_positive := s.bob_positive
  bob_complete := s.bob_complete

/-- The matrix strategy convention is equivalent to the actual Hilbert
tensor-product strategy convention, including all POVM hypotheses. -/
def strategyEncodingEquiv (g : LCS) (dA dB : Nat) : TensorStrategy g dA dB ≃ Strategy g dA dB where
  toFun := TensorStrategy.toMatrix
  invFun := Strategy.toTensor
  left_inv s := by
    cases s
    simp only [TensorStrategy.toMatrix,Strategy.toTensor,thetaTensor_left_inv]
  right_inv s := by
    cases s
    simp only [TensorStrategy.toMatrix,Strategy.toTensor,thetaTensor_right_inv]

def tensorPairWin {g : LCS} {dA dB : Nat} (s : TensorStrategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) : ℝ :=
  if j.val ∈ (g.system.equations[i.val]).vars then
    ∑ a, (inner ℂ s.psi (tensorOperator (s.alice i a) (s.bob j (a j)) s.psi)).re
  else 1

def tensorWin {g : LCS} {dA dB : Nat} (s : TensorStrategy g dA dB) : ℝ :=
  ∑ i, ∑ j, g.pi i j*tensorPairWin s i j

theorem strategyEncoding_pairWin {g : LCS} {dA dB : Nat} (s : TensorStrategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) :
    pairWin s.toMatrix i j=tensorPairWin s i j := by
  simp only [pairWin,tensorPairWin,TensorStrategy.toMatrix,expectation_tensor]

theorem strategyEncoding_win {g : LCS} {dA dB : Nat} (s : TensorStrategy g dA dB) :
    win s.toMatrix=tensorWin s := by
  simp only [win,tensorWin,strategyEncoding_pairWin]

end
end Companion.Analytic
