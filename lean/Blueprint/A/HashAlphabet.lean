import Blueprint.Definitions

namespace Blueprint.Published
noncomputable section
open Companion Companion.Analytic

abbrev HashLetter := Fin 7
abbrev HashWord := List (HashLetter × Bool)

def hashEncode (j : HashLetter) : Nat := j.val+1

/-- The seven named generators in the faithful permutation realization of
the paper's G_P^+. Their numbering is p,q,t,d,x,z,iota. -/
def hashGroupHom : FreeGroup HashLetter →* Concrete.GPplus :=
  Concrete.gpPlusWordHom.comp (FreeGroup.map hashEncode)

/-- Exact named literature input: Mghirbi--Douglas v1.0.0,
Proposition 9.4 (Pauli hash models). The alphabet has precisely seven
letters and the relator collection is a finite set. The conclusion is a
homomorphism into U(D), with both original dimension bounds. No proof is
supplied here. Conversion to arbitrary Nat-indexed words is proved below. -/
def PauliHashModels : Prop := ∀ (W : Finset HashWord) (ell : Nat), 1≤ell →
  (∀ w∈W, w.length≤ell) → (∀ w∈W, hashGroupHom (FreeGroup.mk w)=1) →
  ∀ e : ℝ, 0<e → e≤1 →
  ∃ d : Nat, 0<d ∧ ∃ phi : FreeGroup HashLetter →* Matrix.unitaryGroup (Fin d) ℂ,
    (∀ w∈W, normalizedHS ((phi (FreeGroup.mk w):Mat d)-1)≤e) ∧
    (phi (FreeGroup.of 4):Mat d)*(phi (FreeGroup.of 4):Mat d)=1 ∧
    (phi (FreeGroup.of 5):Mat d)*(phi (FreeGroup.of 5):Mat d)=1 ∧
    (phi ((FreeGroup.of 4*FreeGroup.of 5)^2):Mat d)=-1 ∧
    log2 d≤336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8 ∧
    336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8≤
      400*(ell:ℝ)^2/e^2*log2 (2*ell/e)

end
end Blueprint.Published

namespace Blueprint.AHashProof
noncomputable section
open Companion Companion.Analytic Published

def restrictLetter (a : Nat × Bool) : Option (HashLetter × Bool) :=
  if h : 1≤a.1 ∧ a.1≤7 then some (⟨a.1-1,by omega⟩,a.2) else none

def restrictWord (w : Word) : HashWord := w.filterMap restrictLetter

def restrictHom : FreeGroup Nat →* FreeGroup HashLetter := FreeGroup.lift fun j =>
  if h : 1≤j ∧ j≤7 then FreeGroup.of ⟨j-1,by omega⟩ else 1

theorem restrict_word (w : Word) : restrictHom (FreeGroup.mk w)=FreeGroup.mk (restrictWord w) := by
  induction w with
  | nil => simp [restrictWord,←FreeGroup.one_eq_mk]
  | cons a w ih =>
    simp only [restrictWord,List.filterMap_cons,FreeGroup.lift_mk,List.map_cons,List.prod_cons,
      restrictHom] at *
    rw [ih]
    dsimp only [restrictLetter]
    split
    · cases a.2 <;> simp <;> rfl
    · cases a.2 <;> simp [FreeGroup.lift_mk]

theorem restrict_length (w : Word) : (restrictWord w).length≤w.length := List.length_filterMap_le _ _

theorem unknown_generator (j : Nat) (hj : ¬(1≤j ∧ j≤7)) : Concrete.baseGenerator true j=1 := by
  by_cases h0 : j=0
  · subst j; rfl
  · have hh : 8≤j := by omega
    obtain ⟨k,rfl⟩ : ∃ k, j=k+8 := ⟨j-8,by omega⟩
    rfl

theorem restrict_group : hashGroupHom.comp restrictHom=Concrete.gpPlusWordHom := by
  apply FreeGroup.ext_hom
  intro j
  apply Subtype.ext
  simp only [MonoidHom.comp_apply,restrictHom,FreeGroup.lift_apply_of]
  split
  · rename_i hj
    simp only [hashGroupHom,MonoidHom.comp_apply,FreeGroup.map.of,hashEncode]
    have he : j-1+1=j := by omega
    rw [he]
  · rename_i hj
    simp only [map_one]
    exact (unknown_generator j hj).symm

theorem pulled_assignment {d : Nat}
    (phi : FreeGroup HashLetter →* Matrix.unitaryGroup (Fin d) ℂ) :
    let H := phi.comp restrictHom
    let U : Nat → Mat d := fun j => H (FreeGroup.of j)
    ∀ w : Word, wordEval U w=(phi (FreeGroup.mk (restrictWord w)):Mat d) := by
  dsimp only
  let H := phi.comp restrictHom
  let U : Nat → Mat d := fun j => H (FreeGroup.of j)
  have hU : ∀ j, IsUnitary (U j) := fun j => (H (FreeGroup.of j)).property
  have hh : assignmentHom U hU=H := by
    apply FreeGroup.ext_hom
    intro j
    apply Subtype.ext
    simp only [assignmentHom,FreeGroup.lift_apply_of,asUnitary,U]
  intro w
  change wordEval U w=_
  rw [←assignmentHom_word U hU,hh]
  simp only [H,MonoidHom.comp_apply,restrict_word]

theorem general_hash_models_of_published (hlit : PauliHashModels)
    (R : List Word) (ell : Nat) (hell : 1≤ell)
    (hL : ∀ r∈R, r.length≤ell) (hR : ∀ r∈R, Concrete.gpPlusWordHom (FreeGroup.mk r)=1)
    (e : ℝ) (he : 0<e) (he1 : e≤1) :
    ∃ d : Nat, 0<d ∧ ∃ U : Nat → Mat d, normalizedRepresentation R U e ∧
      U 5*U 5=1 ∧ U 6*U 6=1 ∧ wordEval U lampJ=-1 ∧
      log2 d≤336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8 ∧
      log2 d≤400*(ell:ℝ)^2/e^2*log2 (2*ell/e) := by
  classical
  let W := (R.map restrictWord).toFinset
  have hWL : ∀ w∈W, w.length≤ell := by
    intro w hw
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
    exact (restrict_length r).trans (hL r hr)
  have hWR : ∀ w∈W, hashGroupHom (FreeGroup.mk w)=1 := by
    intro w hw
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
    rw [←restrict_word,←MonoidHom.comp_apply,restrict_group]
    exact hR r hr
  obtain ⟨d,hd,phi,hphi,hx,hz,hJ,hD⟩ := hlit W ell hell hWL hWR e he he1
  let H := phi.comp restrictHom
  let U : Nat → Mat d := fun j => H (FreeGroup.of j)
  refine ⟨d,hd,U,⟨fun j => (H (FreeGroup.of j)).property,?_⟩,?_,?_,?_,
    hD.1,hD.1.trans hD.2⟩
  · intro r hr
    rw [pulled_assignment phi]
    exact hphi _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨r,hr,rfl⟩))
  · exact hx
  · exact hz
  · rw [pulled_assignment phi]
    convert hJ using 1
    congr 2

end
end Blueprint.AHashProof

#print axioms Blueprint.Published.HashLetter
#print axioms Blueprint.Published.HashWord
#print axioms Blueprint.Published.hashEncode
#print axioms Blueprint.Published.hashGroupHom
#print axioms Blueprint.Published.PauliHashModels
#print axioms Blueprint.AHashProof.restrictLetter
#print axioms Blueprint.AHashProof.restrictWord
#print axioms Blueprint.AHashProof.restrictHom
#print axioms Blueprint.AHashProof.restrict_word
#print axioms Blueprint.AHashProof.restrict_length
#print axioms Blueprint.AHashProof.unknown_generator
#print axioms Blueprint.AHashProof.restrict_group
#print axioms Blueprint.AHashProof.pulled_assignment
#print axioms Blueprint.AHashProof.general_hash_models_of_published
