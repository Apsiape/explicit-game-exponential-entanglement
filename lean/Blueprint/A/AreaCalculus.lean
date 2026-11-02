import Blueprint.Definitions

namespace Blueprint.ASector
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def commWord (u v : Word) : Word := u++v++FreeGroup.invRev u++FreeGroup.invRev v
def transportLamp (t : Word) (j : Nat) : Word := t++[(j,true)]++FreeGroup.invRev t
def sourceRelator (i : Fin pauliRelators.length) : FreeGroup Nat := FreeGroup.mk pauliRelators[i.val]

theorem area_one {α ι : Type} (R : ι → FreeGroup α) (n : Nat) : FiniteArea.Area R 1 n :=
  ⟨[],Nat.zero_le _,by simp⟩

theorem area_weaken {α ι : Type} {R : ι → FreeGroup α} {w : FreeGroup α} {a b : Nat}
    (h : FiniteArea.Area R w a) (hab : a≤b) : FiniteArea.Area R w b := by
  obtain ⟨fs,hf,hw⟩ := h
  exact ⟨fs,hf.trans hab,hw⟩

theorem area_mul {α ι : Type} {R : ι → FreeGroup α} {u v : FreeGroup α} {a b : Nat}
    (hu : FiniteArea.Area R u a) (hv : FiniteArea.Area R v b) : FiniteArea.Area R (u*v) (a+b) := by
  obtain ⟨fs,hf,hw⟩ := hu
  obtain ⟨gs,hg,gw⟩ := hv
  exact ⟨fs++gs,by simpa using Nat.add_le_add hf hg,by simp [List.map_append,List.prod_append,hw,gw]⟩

theorem area_inv {α ι : Type} {R : ι → FreeGroup α} {u : FreeGroup α} {a : Nat}
    (hu : FiniteArea.Area R u a) : FiniteArea.Area R u⁻¹ a := by
  obtain ⟨fs,hf,hw⟩ := hu
  let flip : FiniteArea.Factor α ι → FiniteArea.Factor α ι := fun f => (f.1,f.2.1,!f.2.2)
  have hh (f : FiniteArea.Factor α ι) : FiniteArea.factorValue R (flip f)=(FiniteArea.factorValue R f)⁻¹ := by
    rcases f with ⟨g,i,b⟩
    cases b <;> simp [flip,FiniteArea.factorValue,mul_inv_rev,mul_assoc]
  refine ⟨(fs.map flip).reverse,by simpa using hf,?_⟩
  simp only [List.map_reverse,List.map_map,Function.comp_def,hh]
  calc
    _=((fs.map (FiniteArea.factorValue R)).map (fun x => x⁻¹)).reverse.prod := by
      rw [List.map_map]; rfl
    _=((fs.map (FiniteArea.factorValue R)).prod)⁻¹ := (List.prod_inv_reverse _).symm
    _=_ := congrArg (fun x => x⁻¹) hw

theorem area_conj {α ι : Type} {R : ι → FreeGroup α} {u : FreeGroup α} {a : Nat}
    (g : FreeGroup α) (hu : FiniteArea.Area R u a) : FiniteArea.Area R (g*u*g⁻¹) a := by
  obtain ⟨fs,hf,hw⟩ := hu
  let C : FiniteArea.Factor α ι → FiniteArea.Factor α ι := fun f => (g*f.1,f.2.1,f.2.2)
  have hh (f : FiniteArea.Factor α ι) : FiniteArea.factorValue R (C f)=g*FiniteArea.factorValue R f*g⁻¹ := by
    simp [FiniteArea.factorValue,C,mul_assoc]
  refine ⟨fs.map C,by simpa using hf,?_⟩
  simp only [List.map_map,Function.comp_def,hh]
  have hp (ls : List (FiniteArea.Factor α ι)) :
      (ls.map (fun f => g*FiniteArea.factorValue R f*g⁻¹)).prod=g*(ls.map (FiniteArea.factorValue R)).prod*g⁻¹ := by
    induction ls with
    | nil => simp
    | cons f ls ih =>
      simp only [List.map_cons,List.prod_cons]
      rw [ih]
      simp [mul_assoc]
  rw [hp,hw]

def groupComm {α : Type} (u v : FreeGroup α) : FreeGroup α := u*v*u⁻¹*v⁻¹

theorem area_comm_mul {α ι : Type} {R : ι → FreeGroup α} {u v z : FreeGroup α} {a b : Nat}
    (hu : FiniteArea.Area R (groupComm u z) a) (hv : FiniteArea.Area R (groupComm v z) b) :
    FiniteArea.Area R (groupComm (u*v) z) (a+b) := by
  have hh := area_mul (area_conj u hv) hu
  have he : u*groupComm v z*u⁻¹*groupComm u z=groupComm (u*v) z := by
    simp [groupComm,mul_assoc]
  rw [he,Nat.add_comm] at hh
  exact hh

theorem area_comm_inv {α ι : Type} {R : ι → FreeGroup α} {u z : FreeGroup α} {a : Nat}
    (hu : FiniteArea.Area R (groupComm u z) a) : FiniteArea.Area R (groupComm u⁻¹ z) a := by
  have hh := area_conj u⁻¹ (area_inv hu)
  simpa [groupComm,mul_inv_rev,mul_assoc] using hh

def centralFactors (j : Fin 3) : List (FiniteArea.Factor Nat (Fin pauliRelators.length)) :=
  match j.val with
  | 0 => [(1,⟨13,by decide⟩,true),(FreeGroup.mk [(5,true)],⟨14,by decide⟩,true),
      (FreeGroup.mk [(5,true),(6,true)],⟨13,by decide⟩,true),
      (FreeGroup.mk [(5,true),(6,true),(5,true)],⟨14,by decide⟩,true)]
  | 1 => [(1,⟨15,by decide⟩,true),(FreeGroup.mk [(5,true)],⟨16,by decide⟩,true),
      (FreeGroup.mk [(5,true),(6,true)],⟨15,by decide⟩,true),
      (FreeGroup.mk [(5,true),(6,true),(5,true)],⟨16,by decide⟩,true)]
  | _ => [(1,⟨26,by decide⟩,false)]

theorem central_factors_checked : ∀ j : Fin 3,
    (centralFactors j).length≤4 ∧
    ((centralFactors j).map (FiniteArea.factorValue sourceRelator)).prod=
      groupComm (FreeGroup.of (j.val+1)) (FreeGroup.mk lampJ) := by decide +kernel

theorem lampJ_letter_area (a : Nat × Bool) (ha : 1≤a.1 ∧ a.1≤3) :
    FiniteArea.Area sourceRelator (groupComm (FreeGroup.mk [a]) (FreeGroup.mk lampJ)) 4 := by
  let j : Fin 3 := ⟨a.1-1,by omega⟩
  have hnum : j.val+1=a.1 := by dsimp [j]; omega
  have hp : FiniteArea.Area sourceRelator (groupComm (FreeGroup.of a.1) (FreeGroup.mk lampJ)) 4 := by
    refine ⟨centralFactors j,(central_factors_checked j).1,?_⟩
    simpa only [hnum] using (central_factors_checked j).2
  rcases a with ⟨a,b⟩
  cases b
  · change FiniteArea.Area sourceRelator (groupComm (FreeGroup.of a)⁻¹ (FreeGroup.mk lampJ)) 4
    exact area_comm_inv hp
  · exact hp

theorem lampJ_transport_area (T : Word) (hT : ∀ a∈T, 1≤a.1 ∧ a.1≤3) :
    FiniteArea.Area sourceRelator
      (FreeGroup.mk (T++lampJ++FreeGroup.invRev T++FreeGroup.invRev lampJ)) (4*T.length) := by
  have hh : FiniteArea.Area sourceRelator (groupComm (FreeGroup.mk T) (FreeGroup.mk lampJ)) (4*T.length) := by
    induction T with
    | nil =>
      change FiniteArea.Area sourceRelator (groupComm 1 (FreeGroup.mk lampJ)) 0
      simpa only [groupComm,one_mul,inv_one,mul_one,mul_inv_cancel] using area_one sourceRelator 0
    | cons a T ih =>
      have hh := area_comm_mul (lampJ_letter_area a (hT a (by simp)))
        (ih (fun b hb => hT b (List.mem_cons_of_mem a hb)))
      convert hh using 1
      · rw [show FreeGroup.mk (a::T)=FreeGroup.mk [a]*FreeGroup.mk T from by
          simp only [FreeGroup.mul_mk,List.singleton_append]]
      · simp only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm]
  simpa only [groupComm,←FreeGroup.mul_mk,FreeGroup.inv_mk] using hh

end
end Blueprint.ASector

#print axioms Blueprint.ASector.commWord
#print axioms Blueprint.ASector.transportLamp
#print axioms Blueprint.ASector.sourceRelator
#print axioms Blueprint.ASector.area_one
#print axioms Blueprint.ASector.area_weaken
#print axioms Blueprint.ASector.area_mul
#print axioms Blueprint.ASector.area_inv
#print axioms Blueprint.ASector.area_conj
#print axioms Blueprint.ASector.groupComm
#print axioms Blueprint.ASector.area_comm_mul
#print axioms Blueprint.ASector.area_comm_inv
#print axioms Blueprint.ASector.centralFactors
#print axioms Blueprint.ASector.central_factors_checked
#print axioms Blueprint.ASector.lampJ_letter_area
#print axioms Blueprint.ASector.lampJ_transport_area
