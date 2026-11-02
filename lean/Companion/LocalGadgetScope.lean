import Companion.NiceStageBounds

namespace Companion.GeneralGadget
noncomputable section
open DoubleMatrix

def localRow (k : Fin 6) : List Nat :=
  if k=0 then [1,4,5] else if k=1 then [2,5,6] else if k=2 then [6,7,8] else
  if k=3 then [1,8,9] else if k=4 then [3,9,10] else [4,7,10]
@[simp] theorem localRow_length (k : Fin 6) : (localRow k).length=3 := by fin_cases k <;> rfl
def localAt (k : Fin 6) (i : Fin 3) : Nat := (localRow k)[i.val]'(by rw [localRow_length]; exact i.isLt)
theorem localAt_mem : ∀ (k : Fin 6) (i : Fin 3), localAt k i ∈ localRow k := by decide +kernel
theorem localRow_numbers (k : Fin 6) (j : Nat) (hj : j ∈ localRow k) : 1≤j ∧ j≤10 := by
  fin_cases k <;> simp [localRow] at hj
  all_goals rcases hj with rfl|rfl|rfl <;> norm_num

theorem local_scope :
    (∀ i : Fin 10, [(i.val+1,true),(i.val+1,true)] ∈ StageBlocks.stage4Relators) ∧
    (∀ k : Fin 6, (localRow k).map (fun j => (j,true)) ∈ StageBlocks.stage4Relators) ∧
    (∀ (k : Fin 6) (i j : Fin 3),
      [(localAt k i,true),(localAt k j,true),(localAt k i,false),(localAt k j,false)] ∈ StageBlocks.stage4Relators) := by
  decide +kernel

def localVariable (p : Input) (t : NiceTriple p) : Nat → Variable p
  | 0 | 1 => old (niceTriple p t).1
  | 2 => old (niceTriple p t).2.1
  | 3 => old (niceTriple p t).2.2
  | 4 => lamp t 0
  | 5 => lamp t 1
  | 6 => lamp t 2
  | 7 => lamp t 3
  | 8 => lamp t 4
  | 9 => lamp t 5
  | 10 => lamp t 6
  | _ => old (niceTriple p t).1

def insertLocal (p : Input) (t : NiceTriple p) : FreeGroup Nat →* FreeGroup (Option (Variable p)) :=
  FreeGroup.lift (fun j => if j≤10 then FreeGroup.of (some (localVariable p t j)) else 1)

theorem localRow_map (p : Input) (t : NiceTriple p) (k : Fin 6) :
    (localRow k).map (localVariable p t)=(systemEquation p (.inr (t,k))).vars := by
  rcases ht : niceTriple p t with ⟨a,b,c⟩
  fin_cases k <;> simp [localRow,localVariable,systemEquation,ht]

theorem local_row_position (p : Input) (t : NiceTriple p) (k : Fin 6) (a : Variable p)
    (ha : a ∈ (systemEquation p (.inr (t,k))).vars) :
    ∃ i : Fin 3, localVariable p t (localAt k i)=a := by
  rw [← localRow_map] at ha
  obtain ⟨i,hi⟩ := List.get_of_mem ha
  have hib : i.val<3 := by simpa using i.isLt
  refine ⟨⟨i.val,hib⟩,?_⟩
  simpa [localAt,List.get_eq_getElem] using hi

theorem insertLocal_row (p : Input) (t : NiceTriple p) (k : Fin 6) (j : Nat) (hj : j ∈ localRow k) :
    insertLocal p t (FreeGroup.of j)=FreeGroup.of (some (localVariable p t j)) := by
  simp [insertLocal,(localRow_numbers k j hj).2]
theorem insertLocal_y (p : Input) (t : NiceTriple p) (k : Fin 7) :
    insertLocal p t (FreeGroup.of (k.val+4))=FreeGroup.of (some (lamp t k)) := by
  fin_cases k <;> simp [insertLocal,localVariable]

theorem mk_positive (xs : List Nat) :
    FreeGroup.mk (xs.map (fun j => (j,true)))=(xs.map FreeGroup.of).prod := by
  induction xs with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons a xs ih =>
    change FreeGroup.mk ([(a,true)]++xs.map (fun j => (j,true)))=FreeGroup.of a*(xs.map FreeGroup.of).prod
    rw [← FreeGroup.mul_mk,ih]
    rfl
theorem mk_commutator (a b : Nat) :
    FreeGroup.mk [(a,true),(b,true),(a,false),(b,false)]=commWord (FreeGroup.of a) (FreeGroup.of b) := by
  simp only [commWord,FreeGroup.of,FreeGroup.inv_mk,FreeGroup.mul_mk]
  rfl

theorem local_square_map (p : Input) (t : NiceTriple p) (k : Fin 7) :
    insertLocal p t (FreeGroup.mk [(k.val+4,true),(k.val+4,true)])=
      FreeGroup.of (some (lamp t k))*FreeGroup.of (some (lamp t k)) := by
  change insertLocal p t (FreeGroup.of (k.val+4)*FreeGroup.of (k.val+4))=_
  rw [map_mul,insertLocal_y]

theorem local_product_map (p : Input) (t : NiceTriple p) (k : Fin 6) :
    insertLocal p t (FreeGroup.mk ((localRow k).map (fun j => (j,true))))=
      solutionRelator p (.inr (.inr (.inl (.inr (t,k))))) := by
  rw [mk_positive,map_list_prod,List.map_map]
  simp only [Function.comp_def]
  have hm : (localRow k).map (fun j => insertLocal p t (FreeGroup.of j))=
      (localRow k).map (fun j => FreeGroup.of (some (localVariable p t j))) := by
    apply List.map_congr_left
    intro j hj
    exact insertLocal_row p t k j hj
  rw [hm]
  change _=(1:FreeGroup (Option (Variable p)))*
    ((systemEquation p (.inr (t,k))).vars.map (fun a => FreeGroup.of (some a))).prod
  rw [one_mul,← localRow_map,List.map_map]
  rfl

variable {α : Type} [Fintype α] [DecidableEq α]
def finalStageHom (p : Input) (gamma : Nice p → U α) : FreeGroup (Option (Variable p)) →* U (Bool × α) :=
  FreeGroup.lift (fun a => a.elim (ScalarPhase.minusOne (Bool × α)) (fourthStage p gamma))
def localPhi (p : Input) (gamma : Nice p → U α) (t : NiceTriple p) : FreeGroup Nat →* U (Bool × α) :=
  let (a,b,c) := niceTriple p t
  StageValues.stage4 (gamma a) (gamma b) (gamma c)

theorem final_local (p : Input) (gamma : Nice p → U α) (t : NiceTriple p) :
    (finalStageHom p gamma).comp (insertLocal p t)=localPhi p gamma t := by
  rcases ht : niceTriple p t with ⟨a,b,c⟩
  apply FreeGroup.ext_hom
  intro j
  rcases j with _|_|_|_|_|_|_|_|_|_|_|j
  all_goals simp [finalStageHom,insertLocal,localVariable,localPhi,fourthStage,old,lamp,ht,Option.elim_some,
    StageValues.stage4,BlockExtension.hom,BlockExtension.blockAt,BlockExtension.value,
    StageBlocks.stage4Assignments,StageValues.tripleHom,FreeGroup.lift_mk,mul_assoc,mono_one]
  all_goals split <;> try omega
  all_goals simp [mono_one]

end
end Companion.GeneralGadget
