import Blueprint.A.HoughtonCollectionArea
import Blueprint.A.HoughtonNumerics

namespace Blueprint.Published
noncomputable section
open Companion HoughtonProof

/-- Corollary A.5 at its exact original proposition: both finite
presentations, the Dehn comparison and the original numerical bound. -/
theorem houghtonDehnCorollary : HoughtonDehnCorollary := by
  intro n hn
  refine ⟨houghton_filling_exists n hn,johnson_filling_exists n hn,
    houghton_dehn_comparison_unconditional n hn,?_⟩
  exact (Nat.cast_le.mpr (johnson_dehn_collection n hn)).trans (collection_numeric_bound n hn)

end
end Blueprint.Published

#print axioms Blueprint.Published.houghtonDehnCorollary
