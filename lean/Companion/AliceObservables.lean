import Companion.PolarStandardForm

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def boolPhase (b : Bool) : ℂ := if b then -1 else 1

theorem boolPhase_xor (b c : Bool) : boolPhase (Bool.xor b c)=boolPhase b*boolPhase c := by
  cases b <;> cases c <;> norm_num [boolPhase]

theorem boolPhase_foldl (L : List Bool) (b : Bool) :
    boolPhase (L.foldl Bool.xor b)=boolPhase b*(L.map boolPhase).prod := by
  induction L generalizing b with
  | nil => simp
  | cons c L ih => simp only [List.foldl_cons,ih,boolPhase_xor,List.map_cons,List.prod_cons,mul_assoc]

theorem boolPhase_parity (L : List Bool) :
    (L.map boolPhase).prod=boolPhase (L.foldl Bool.xor false) := by
  simpa only [boolPhase,Bool.false_eq_true,↓reduceIte,one_mul] using (boolPhase_foldl L false).symm

def outcomeObservable {n d : Nat} (P : QIT.ProjectiveMeasurement (Fin n → Bool) (Fin d)) (j : Fin n) : Mat d :=
  pvmFunction P (fun a => bitSign a j)

theorem outcomeObservable_involution {n d : Nat} (P : QIT.ProjectiveMeasurement (Fin n → Bool) (Fin d))
    (j : Fin n) : IsInvolution (outcomeObservable P j) := by
  have hs (a : Fin n → Bool) : star (bitSign a j)=bitSign a j := by
    cases h : a j <;> simp [bitSign,h]
  have hm : (fun a : Fin n → Bool => bitSign a j*bitSign a j)=(fun _ => (1:ℂ)) := by
    funext a
    cases h : a j <;> simp [bitSign,h]
  constructor
  · rw [outcomeObservable,pvmFunction_conjTranspose]
    simp only [hs]
  · rw [outcomeObservable,pvmFunction_mul,hm,pvmFunction_one]

theorem outcomeObservable_commute {n d : Nat} (P : QIT.ProjectiveMeasurement (Fin n → Bool) (Fin d))
    (i j : Fin n) : Commute (outcomeObservable P i) (outcomeObservable P j) := pvmFunction_commute P _ _

theorem outcomeObservable_transpose {n d : Nat} (P : QIT.ProjectiveMeasurement (Fin n → Bool) (Fin d))
    (j : Fin n) : (outcomeObservable P j).transpose=outcomeObservable (transposePVM P) j :=
  pvmFunction_transpose P _

def indexedAliceObservable {g : LCS} {d : Nat}
    (P : QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin d)) (j : Nat) : Mat d :=
  pvmFunction P (fun a => boolPhase (answerBit g a j))

theorem indexedAliceObservable_fin {g : LCS} {d : Nat}
    (P : QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin d)) (j : Fin g.system.n) :
    indexedAliceObservable P j.val=outcomeObservable P j := by
  unfold indexedAliceObservable outcomeObservable
  congr 1
  funext a
  simp [answerBit,j.isLt,boolPhase,bitSign]

/-- The recorded equation order gives exactly the required Alice parity
product, because every nonzero projective answer satisfies that equation. -/
theorem alice_equation_product {g : LCS} {d : Nat}
    (i : Fin g.system.equations.length)
    (P : QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin d))
    (hv : ∀ a, ¬validAnswer g i a → P.effects a=0) :
    (((g.system.equations[i.val]).vars.map (indexedAliceObservable P)).prod)=
      boolPhase (g.system.equations[i.val]).rhs • (1:Mat d) := by
  let vars := (g.system.equations[i.val]).vars
  let fs := vars.map (fun j => fun a => boolPhase (answerBit g a j))
  have he : (vars.map (indexedAliceObservable P)).prod=
      pvmFunction P (fun a => (vars.map (fun j => boolPhase (answerBit g a j))).prod) := by
    change (vars.map (fun j => pvmFunction P (fun a => boolPhase (answerBit g a j)))).prod=_
    simpa only [fs,List.map_map,Function.comp_def] using pvmFunction_product P fs
  change (vars.map (indexedAliceObservable P)).prod=_
  rw [he,← pvmFunction_constant P (boolPhase (g.system.equations[i.val]).rhs)]
  unfold pvmFunction
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : validAnswer g i a
  · have hphase := boolPhase_parity (vars.map (answerBit g a))
    have hpar : (vars.map (answerBit g a)).foldl Bool.xor false=(g.system.equations[i.val]).rhs := ha
    simp only [List.map_map,Function.comp_def,hpar] at hphase
    change (vars.map (fun j => boolPhase (answerBit g a j))).prod • P.effects a=
      boolPhase (g.system.equations[i.val]).rhs • P.effects a
    rw [hphase]
  · rw [hv a ha]
    simp

end
end Companion.Analytic.TransferProof
