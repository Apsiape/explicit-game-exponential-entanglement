import Blueprint.A.SpatialScore
import Companion.ReturnBranchEncoding

namespace Blueprint.SpatialProof
noncomputable section
open Companion Companion.Analytic
open ReturnProof

/-- S_i in the literature, indexed in the row's recorded increasing order. -/
def PaperAnswer (g : LCS) (i : Fin g.system.equations.length) :=
  {a : Fin (g.system.equations[i.val]).vars.length → Bool // recordParity a=(g.system.equations[i.val]).rhs}

noncomputable instance paperAnswerFintype (g : LCS) (i : Fin g.system.equations.length) :
    Fintype (PaperAnswer g i) := by
  classical
  unfold PaperAnswer
  infer_instance

def readRow (g : LCS) (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) :
    Fin (g.system.equations[i.val]).vars.length → Bool := fun k => a (rowIndex g i k)

theorem valid_congr_on_row (g : LCS) (i : Fin g.system.equations.length)
    (a b : Fin g.system.n → Bool)
    (h : ∀ j : Fin g.system.n, j.val∈(g.system.equations[i.val]).vars → a j=b j) :
    validAnswer g i a ↔ validAnswer g i b := by
  have hh : (g.system.equations[i.val]).vars.map (answerBit g a)=
      (g.system.equations[i.val]).vars.map (answerBit g b) := by
    apply List.map_congr_left
    intro j hj
    have hb := TransferProof.row_variable_bound g i j hj
    simpa only [answerBit,dif_pos hb] using h ⟨j,hb⟩ hj
  unfold validAnswer
  rw [hh]

theorem readRow_valid (g : LCS) (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool)
    (ha : validAnswer g i a) : recordParity (readRow g i a)=(g.system.equations[i.val]).rhs := by
  apply (validAnswer_rowRecord g i (readRow g i a)).mp
  apply (valid_congr_on_row g i _ a ?_).mpr ha
  intro j hj
  obtain ⟨k,rfl⟩ := (rowIndex_range g i j).mpr hj
  exact rowRecord_apply g i (readRow g i a) k

def correctedRecord (g : LCS) (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) :
    PaperAnswer g i :=
  ⟨readRow g i (correctedAnswer g i a),readRow_valid g i _ (correctedAnswer_valid g i a)⟩

theorem correctedRecord_bit (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin g.system.n → Bool) (ha : validAnswer g i a) (j : Fin g.system.n)
    (hj : j.val∈(g.system.equations[i.val]).vars) :
    rowRecord g i (correctedRecord g i a).val j=a j := by
  obtain ⟨k,rfl⟩ := (rowIndex_range g i j).mpr hj
  rw [rowRecord_apply]
  exact congrFun (correctedAnswer_fixed_valid g i a ha) (rowIndex g i k)

theorem paperAnswer_valid (g : LCS) (i : Fin g.system.equations.length) (a : PaperAnswer g i) :
    validAnswer g i (rowRecord g i a.val) := (validAnswer_rowRecord g i a.val).mpr a.property

theorem paperAnswer_nonempty (g : LCS) (i : Fin g.system.equations.length) : Nonempty (PaperAnswer g i) :=
  ⟨correctedRecord g i (fun _ => false)⟩

end
end Blueprint.SpatialProof

#print axioms Blueprint.SpatialProof.PaperAnswer
#print axioms Blueprint.SpatialProof.paperAnswerFintype
#print axioms Blueprint.SpatialProof.readRow
#print axioms Blueprint.SpatialProof.valid_congr_on_row
#print axioms Blueprint.SpatialProof.readRow_valid
#print axioms Blueprint.SpatialProof.correctedRecord
#print axioms Blueprint.SpatialProof.correctedRecord_bit
#print axioms Blueprint.SpatialProof.paperAnswer_valid
#print axioms Blueprint.SpatialProof.paperAnswer_nonempty
