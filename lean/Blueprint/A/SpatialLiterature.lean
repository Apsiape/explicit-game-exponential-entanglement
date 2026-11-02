import Blueprint.A.SpatialProjective
import Blueprint.A.SpatialAnswers

namespace Blueprint.Published
noncomputable section
open Companion Companion.Analytic SpatialProof TransferProof
open scoped BigOperators

/-- Definition 1 in Cleve--Liu--Slofstra: a finite-dimensional operator
solution of the binary linear system. The row indices are in increasing order. -/
def FiniteOperatorSolution (g : LCS) : Prop :=
  ∃ d : Nat, 0<d ∧ ∃ B : Fin g.system.n → Mat d,
    (∀ j, IsInvolution (B j)) ∧
    (∀ (i : Fin g.system.equations.length) (j k : Fin g.system.n),
      j.val∈(g.system.equations[i.val]).vars → k.val∈(g.system.equations[i.val]).vars →
      B j*B k=B k*B j) ∧
    (∀ i : Fin g.system.equations.length,
      ((g.system.equations[i.val]).vars.map (TransferProof.naturalBob B)).prod=
        boolPhase (g.system.equations[i.val]).rhs • (1:Mat d))

/-- Exact literature input: Cleve--Liu--Slofstra, "Perfect commuting-operator
strategies for linear system games", arXiv:1606.02278v1 (2016), Theorem 5,
implication (1) => (2). The input is a perfect tensor-product strategy with
projective measurements on S_i, not the project's weighted POVM convention.
The theorem explicitly allows nonseparable local Hilbert spaces (paragraph
following Theorem 5). No proof of this literature statement is supplied here.

Source: https://arxiv.org/html/1606.02278v1 -/
def TensorPerfectFinite : Prop := by
  classical
  exact ∀ (g : LCS) (E F : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (psi : SpatialTensor E F)
    (A : (i : Fin g.system.equations.length) → PaperAnswer g i → E →L[ℂ] E)
    (B : Fin g.system.n → Bool → F →L[ℂ] F),
  ‖psi‖=1 → (∀ i, PVM (A i)) → (∀ j, PVM (B j)) →
  (∀ (i : Fin g.system.equations.length) (j : Fin g.system.n),
    j.val∈(g.system.equations[i.val]).vars →
    ∑ a : PaperAnswer g i, expect psi (A i a) (B j (ReturnProof.rowRecord g i a.val j))=1) →
  FiniteOperatorSolution g

end
end Blueprint.Published

#print axioms Blueprint.Published.FiniteOperatorSolution
#print axioms Blueprint.Published.TensorPerfectFinite
