import Blueprint.A.Diagram.Conjugators
import Blueprint
namespace Blueprint.DiagramProof
/-- Theorem A with the sole permitted published input. -/
theorem theoremA (hspatial : Published.TensorPerfectFinite) : AStatement :=
  Blueprint.theoremA hspatial
end Blueprint.DiagramProof
#print axioms Blueprint.DiagramProof.shelling
#print axioms Blueprint.DiagramProof.conjugatorLengths
#print axioms Blueprint.DiagramProof.theoremA
