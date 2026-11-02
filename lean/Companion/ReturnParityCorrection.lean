import Companion.BranchHilbertSchmidt

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

/-- The actual last-bit correction in ReturnSpecification always produces
a valid answer, using nonempty, bounded, duplicate-free equation rows. -/
theorem correctedAnswer_valid (g : LCS) (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) :
    validAnswer g i (correctedAnswer g i a) := by
  classical
  by_cases ha : validAnswer g i a
  · simpa only [correctedAnswer,ha,↓reduceIte] using ha
  let vs := (g.system.equations[i.val]).vars
  have hne : vs≠[] := g.rows_nonempty _ (List.getElem_mem i.isLt)
  let j := vs.getLast hne
  let pre := vs.dropLast
  have hsplit : vs=pre++[j] := (List.dropLast_concat_getLast hne).symm
  have hnodup : vs.Nodup := g.rows_nodup _ (List.getElem_mem i.isLt)
  rw [hsplit] at hnodup
  have hjnot (k : Nat) (hk : k∈pre) : k≠j :=
    (List.nodup_append.mp hnodup).2.2 k hk j (by simp)
  have hjmem : j∈vs := by rw [hsplit]; simp
  have hj : j<g.system.n := TransferProof.row_variable_bound g i j hjmem
  let f : Fin g.system.n → Bool := fun b => if b.val=j then !(a b) else a b
  have hpre : pre.map (answerBit g f)=pre.map (answerBit g a) := by
    apply List.map_congr_left
    intro k hk
    by_cases hb : k<g.system.n <;> simp [answerBit,f,hb,hjnot k hk]
  have hjbit : answerBit g f j= !(answerBit g a j) := by simp [answerBit,f,hj]
  have hflip : (vs.map (answerBit g f)).foldl Bool.xor false= !((vs.map (answerBit g a)).foldl Bool.xor false) := by
    rw [hsplit,List.map_append,List.map_append,hpre]
    simp only [List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil,hjbit]
    cases (pre.map (answerBit g a)).foldl Bool.xor false <;> cases answerBit g a j <;> rfl
  have hnot : (vs.map (answerBit g a)).foldl Bool.xor false≠(g.system.equations[i.val]).rhs := ha
  have htarget : (!((vs.map (answerBit g a)).foldl Bool.xor false))=(g.system.equations[i.val]).rhs := by
    cases hp : (vs.map (answerBit g a)).foldl Bool.xor false <;>
      cases hr : (g.system.equations[i.val]).rhs <;> simp_all
  have hlast : vs.getLast?.getD 0=j := by rw [List.getLast?_eq_some_getLast hne]; rfl
  rw [correctedAnswer,ite_eq_right ha]
  change validAnswer g i (fun b => if b.val=vs.getLast?.getD 0 then !(a b) else a b)
  rw [hlast]
  change (vs.map (answerBit g f)).foldl Bool.xor false=(g.system.equations[i.val]).rhs
  exact hflip.trans htarget

theorem correctedAnswer_fixed_valid (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin g.system.n → Bool) (ha : validAnswer g i a) : correctedAnswer g i a=a := by
  classical
  simp only [correctedAnswer,ha,↓reduceIte]

theorem correctedAnswer_agrees_except_last (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin g.system.n → Bool) (j : Fin g.system.n)
    (hj : j.val≠(g.system.equations[i.val]).vars.getLast?.getD 0) : correctedAnswer g i a j=a j := by
  classical
  by_cases ha : validAnswer g i a <;> simp [correctedAnswer,ha,hj]

theorem correctedAnswer_change_implies_invalid (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin g.system.n → Bool) (hchange : correctedAnswer g i a≠a) : ¬validAnswer g i a := by
  intro ha
  exact hchange (correctedAnswer_fixed_valid g i a ha)

/-- Positivity of precisely the prescribed sequential Alice effects. -/
theorem sequentialAlice_positive {d : Nat} (g : LCS) (B : Fin g.system.n → Mat d)
    (i : Fin g.system.equations.length) (out : Fin g.system.n → Bool) :
    (sequentialAlice g B i out).PosSemidef := by
  classical
  unfold sequentialAlice
  apply Matrix.posSemidef_sum
  intro a _
  split
  · exact Matrix.posSemidef_conjTranspose_mul_self _
  · exact Matrix.PosSemidef.zero

/-- Invalid answers have zero effect in the actual return measurement. -/
theorem sequentialAlice_invalid {d : Nat} (g : LCS) (B : Fin g.system.n → Mat d)
    (i : Fin g.system.equations.length) (out : Fin g.system.n → Bool) (hout : ¬validAnswer g i out) :
    sequentialAlice g B i out=0 := by
  classical
  unfold sequentialAlice
  apply Finset.sum_eq_zero
  intro a _
  have hne : correctedAnswer g i a≠out := fun h => hout (h ▸ correctedAnswer_valid g i a)
  simp [hne]

end
end Companion.Analytic.ReturnProof
