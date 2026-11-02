import Companion.ProjectiveConsistency

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def variableAppears (g : LCS) (j : Fin g.system.n) : Prop :=
  ∃ i : Fin g.system.equations.length, j.val ∈ (g.system.equations[i.val]).vars

def usedBob {g : LCS} {r : Nat} (B : Fin g.system.n → Mat r) (j : Fin g.system.n) : Mat r := by
  classical
  exact if variableAppears g j then B j else 1

theorem usedBob_involution {g : LCS} {r : Nat} (B : Fin g.system.n → Mat r)
    (hB : ∀ j, IsInvolution (B j)) (j : Fin g.system.n) : IsInvolution (usedBob B j) := by
  classical
  by_cases h : variableAppears g j
  · simpa only [usedBob,h,↓reduceIte] using hB j
  · simp [usedBob,h,IsInvolution]

theorem usedBob_in_row {g : LCS} {r : Nat} (B : Fin g.system.n → Mat r)
    (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars) : usedBob B j=B j := by
  classical
  simp only [usedBob,show variableAppears g j from ⟨i,hj⟩,↓reduceIte]

def naturalBob {n r : Nat} (B : Fin n → Mat r) (j : Nat) : Mat r :=
  if h : j<n then B ⟨j,h⟩ else 1

theorem naturalBob_fin {n r : Nat} (B : Fin n → Mat r) (j : Fin n) : naturalBob B j.val=B j := by
  simp [naturalBob,j.isLt]

def solutionAssignment {n r : Nat} (B : Fin n → Mat r) (j : Nat) : Mat r :=
  if h : 1≤j ∧ j≤n then B ⟨j-1,by omega⟩ else if j=n+1 then -1 else 1

theorem solutionAssignment_generator {n r : Nat} (B : Fin n → Mat r) (j : Fin n) :
    solutionAssignment B (j.val+1)=B j := by
  have h : 1≤j.val+1 ∧ j.val+1≤n := by constructor <;> omega
  unfold solutionAssignment
  rw [dite_eq_left h]
  congr 1

theorem solutionAssignment_J {n r : Nat} (B : Fin n → Mat r) : solutionAssignment B (n+1)= -1 := by
  have h : ¬(1≤n+1 ∧ n+1≤n) := by omega
  simp [solutionAssignment,h]

theorem solutionAssignment_involution {n r : Nat} (B : Fin n → Mat r)
    (hB : ∀ j, IsInvolution (B j)) (j : Nat) : IsInvolution (solutionAssignment B j) := by
  unfold solutionAssignment
  split
  · exact hB _
  · split <;> simp [IsInvolution]

theorem wordEval_append {r : Nat} (U : Nat → Mat r) (v w : Word) :
    wordEval U (v++w)=wordEval U v*wordEval U w := by
  simp only [wordEval,List.map_append,List.prod_append]

theorem wordEval_solution_square {n r : Nat} (B : Fin n → Mat r) (hB : ∀ j, IsInvolution (B j)) (j : Fin n) :
    wordEval (solutionAssignment B) [pos j.val,pos j.val]=1 := by
  simp only [wordEval,pos,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    ↓reduceIte,solutionAssignment_generator,Matrix.mul_one,(hB j).2]

theorem wordEval_solution_centralSquare {n r : Nat} (B : Fin n → Mat r) :
    wordEval (solutionAssignment B) [pos n,pos n]=1 := by
  simp [wordEval,pos,solutionAssignment_J]

theorem wordEval_solution_commute {n r : Nat} (B : Fin n → Mat r) (hB : ∀ j, IsInvolution (B j))
    (j k : Fin n) :
    wordEval (solutionAssignment B) [pos j.val,pos k.val,neg j.val,neg k.val]=B j*B k*B j*B k := by
  simp only [wordEval,pos,neg,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Bool.false_eq_true,↓reduceIte,solutionAssignment_generator,(hB j).1,(hB k).1,Matrix.mul_one,Matrix.mul_assoc]

theorem wordEval_solution_central {n r : Nat} (B : Fin n → Mat r) (hB : ∀ j, IsInvolution (B j)) (j : Fin n) :
    wordEval (solutionAssignment B) [pos j.val,pos n,neg j.val,neg n]=1 := by
  simp only [wordEval,pos,neg,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Bool.false_eq_true,↓reduceIte,solutionAssignment_generator,solutionAssignment_J,(hB j).1,Matrix.conjTranspose_neg,
    Matrix.conjTranspose_one,Matrix.mul_one,Matrix.one_mul,Matrix.mul_neg,Matrix.neg_mul,neg_neg]
  exact (hB j).2

theorem wordEval_solution_row {n r : Nat} (B : Fin n → Mat r) (vars : List Nat) (rhs : Bool)
    (hb : ∀ j ∈ vars, j<n) :
    wordEval (solutionAssignment B) ((if rhs then [pos n] else [])++vars.map pos)=
      boolPhase rhs • (vars.map (naturalBob B)).prod := by
  have he : wordEval (solutionAssignment B) (vars.map pos)=(vars.map (naturalBob B)).prod := by
    unfold wordEval
    simp only [List.map_map,Function.comp_def,pos,↓reduceIte]
    apply congrArg List.prod
    apply List.map_congr_left
    intro j hj
    have h := solutionAssignment_generator B (⟨j,hb j hj⟩:Fin n)
    simpa only [naturalBob,hb j hj,↓reduceDIte] using h
  rw [wordEval_append,he]
  cases rhs <;> simp [wordEval,pos,solutionAssignment_J,boolPhase]

theorem row_variable_bound (g : LCS) (i : Fin g.system.equations.length) (j : Nat)
    (hj : j ∈ (g.system.equations[i.val]).vars) : j<g.system.n :=
  g.rows_bounded _ (List.getElem_mem i.isLt) j hj

end
end Companion.Analytic.TransferProof
