import Blueprint.A.Diagram.Initial
import Blueprint.A.Diagram.Folding
import Blueprint.A.Diagram.Outer
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
set_option maxHeartbeats 800000
/-- Whole finite-diagram induction; all diagram primitives are separately named. -/
theorem shelling {R : Finset Word} {K n : Nat} {u : Word} (d : Diagram R K u n) :
    ∃ m, m ≤ n ∧ Shelling R K u m := by
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    rcases Blueprint.DiagramProof.outer d with ht | hc
    · exact ⟨0,Nat.zero_le _,Shelling.tree u ht⟩
    · obtain ⟨c⟩ := hc
      obtain ⟨v,j,hj,⟨face⟩,⟨rest⟩⟩ := collapse c
      obtain ⟨m,hm,sm⟩ := ih j (by omega) rest
      exact ⟨m+1,by omega,Shelling.face face sm⟩
/-- Complete finite-map proof at the original ConjugatorLengths proposition type. -/
theorem conjugatorLengths : Published.ConjugatorLengths := by
  intro R K k w hR ha
  have ha' : finiteWordArea R (FreeGroup.reduce w) k := by
    simpa only [finiteWordArea,FreeGroup.reduce.self] using ha
  obtain ⟨n,hn,⟨d⟩⟩ := initial R K k (FreeGroup.reduce w) hR ha'
  obtain ⟨m,hm,sm⟩ := shelling d
  exact factors_of_reduced_shelling R K k w ⟨m,hm.trans hn,sm⟩
end Blueprint.DiagramProof
