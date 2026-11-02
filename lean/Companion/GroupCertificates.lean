import Companion.LampModel
import Companion.LampFaithfulness
import Companion.Derivations

namespace Companion.Concrete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem c1_checks : pauliRelators.all (wordIdentityCheck false)=true := by decide +kernel

/-- The 27 certificate words are identities as permutations of the full
phase-and-register space, not merely in a finite truncation. -/
theorem c1_permutations : ∀ w ∈ pauliRelators, wordPermutation false w=1 := by
  intro w hw
  exact wordIdentityCheck_sound (List.all_eq_true.mp c1_checks w hw)

def gpWordHom : FreeGroup Nat →* GP := (wordHom false).rangeRestrict
def gpPlusWordHom : FreeGroup Nat →* GPplus := (wordHom true).rangeRestrict

theorem c1_group : ∀ w ∈ pauliRelators, gpWordHom (FreeGroup.mk w)=1 := by
  intro w hw
  apply Subtype.ext
  exact c1_permutations w hw

theorem gp_j_nontrivial : gpWordHom (FreeGroup.mk jWord)≠1 := by
  intro h
  exact j_nontrivial false (congrArg Subtype.val h)

theorem gpPlus_j_nontrivial : gpPlusWordHom (FreeGroup.mk jWord)≠1 := by
  intro h
  exact j_nontrivial true (congrArg Subtype.val h)

end Companion.Concrete
