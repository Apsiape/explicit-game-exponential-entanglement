import Blueprint.A.HashClockInterior

namespace Blueprint.AHash
noncomputable section
open Companion Concrete Companion.Analytic
open scoped Classical
set_option maxHeartbeats 400000

abbrev ClockHash (m k : Nat) := (Fin k → Fin (3*(2*m+3)) → Bool) × (Fin k → Bool)
abbrev ClockRegister (k : Nat) := (Fin k → Bool) → Bool
abbrev ClockFibre (m k : Nat) := ClockHash m k × ClockRegister k
abbrev ClockModelIndex (m k : Nat) := FiniteClock m × ClockFibre m k

def clockHostFibre (m k : Nat) (a : HostLetter) (c : FiniteClock m) :
    Matrix (ClockFibre m k) (ClockFibre m k) ℂ :=
  if hc : ClockInside m (clockMove a (clockRead c)) then
    hashAction (k:=k) (finiteHostAffine (2*m+3) (hostClockCocycle a (clockRead c))
      (hostClockCocycle_boxFixed a (clockRead c) m
        (clockRead_inside c).1 (clockRead_inside c).2 hc.1 hc.2)) 0 0 0
  else 1

theorem clockHostFibre_unitary (m k : Nat) (a : HostLetter) (c : FiniteClock m) :
    (clockHostFibre m k a c).conjTranspose*clockHostFibre m k a c=1 ∧
      clockHostFibre m k a c*(clockHostFibre m k a c).conjTranspose=1 := by
  unfold clockHostFibre
  split
  · exact hashAction_unitary _ _ _ _
  · simp only [Matrix.conjTranspose_one,Matrix.one_mul,and_self]

theorem clockHostFibre_correct (m k : Nat) (a : HostLetter) (c : FiniteClock m)
    (hc : ClockInside m (clockMove a (clockRead c))) :
    clockHostFibre m k a c=
      hashAction (k:=k) (finiteHostAffine (2*m+3) (hostClockCocycle a (clockRead c))
        (hostClockCocycle_boxFixed a (clockRead c) m
          (clockRead_inside c).1 (clockRead_inside c).2 hc.1 hc.2)) 0 0 0 := by
  simp only [clockHostFibre,dite_eq_left hc]

def clockHostMatrix (m k : Nat) (a : HostLetter) : Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ :=
  blockMatrix (finiteClockMove m a).symm (fun c => clockHostFibre m k a ((finiteClockMove m a).symm c))

theorem clockHostMatrix_unitary (m k : Nat) (a : HostLetter) :
    (clockHostMatrix m k a).conjTranspose*clockHostMatrix m k a=1 ∧
      clockHostMatrix m k a*(clockHostMatrix m k a).conjTranspose=1 := by
  have hh := blockMatrix_unitary (β:=FiniteClock m) (finiteClockMove m a).symm
    (fun c => clockHostFibre m k a ((finiteClockMove m a).symm c))
    (fun c => clockHostFibre_unitary m k a ((finiteClockMove m a).symm c))
  refine ⟨hh.1.trans ?_,hh.2.trans ?_⟩
  all_goals ext i j; by_cases h : i=j <;> simp [Matrix.one_apply,h]

theorem diagonalBlocks_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (A B : β → Matrix α α ℂ) :
    blockMatrix (1:Equiv.Perm β) A*blockMatrix (1:Equiv.Perm β) B=
      blockMatrix (1:Equiv.Perm β) (fun b => A b*B b) := by
  rw [blockMatrix_mul]
  rfl

theorem diagonalBlocks_neg_one {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] :
    blockMatrix (1:Equiv.Perm β) (fun _ => -(1:Matrix α α ℂ))= -1 := by
  ext ⟨b,i⟩ ⟨c,j⟩
  by_cases h : b=c <;> simp [blockMatrix,Matrix.one_apply,Prod.mk.injEq,h]

theorem diagonalBlocks_exact {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A B : β → Matrix α α ℂ)
    (hAB : ∀ b, A b*A b=1 ∧ B b*B b=1 ∧ A b*B b*A b*B b= -1) :
    let X := blockMatrix (1:Equiv.Perm β) A
    let Z := blockMatrix (1:Equiv.Perm β) B
    X*X=1 ∧ Z*Z=1 ∧ X*Z*X*Z= -1 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [diagonalBlocks_mul,show (fun b => A b*A b)=(fun _ => 1) from funext (fun b => (hAB b).1),blockMatrix_one]
  · rw [diagonalBlocks_mul,show (fun b => B b*B b)=(fun _ => 1) from funext (fun b => (hAB b).2.1),blockMatrix_one]
  · rw [diagonalBlocks_mul,diagonalBlocks_mul,diagonalBlocks_mul,
      show (fun b => A b*B b*A b*B b)=(fun _ => -1) from funext (fun b => (hAB b).2.2),diagonalBlocks_neg_one]

def clockLampFibre (m k : Nat) (isZ : Bool) : Matrix (ClockFibre m k) (ClockFibre m k) ℂ :=
  hashAction (k:=k) (1 : (Fin (3*(2*m+3)) → Bool) ≃ᵃ[Bool] (Fin (3*(2*m+3)) → Bool))
    0 (if isZ then 0 else siteMask 0) (if isZ then siteMask 0 else 0)

theorem clockLampFibre_unitary (m k : Nat) (isZ : Bool) :
    (clockLampFibre m k isZ).conjTranspose*clockLampFibre m k isZ=1 ∧
      clockLampFibre m k isZ*(clockLampFibre m k isZ).conjTranspose=1 :=
  hashAction_unitary _ _ _ _

theorem clockLampFibre_exact (m k : Nat) :
    clockLampFibre m k false*clockLampFibre m k false=1 ∧
      clockLampFibre m k true*clockLampFibre m k true=1 ∧
      clockLampFibre m k false*clockLampFibre m k true*
        clockLampFibre m k false*clockLampFibre m k true= -1 := by
  simp only [clockLampFibre,Bool.false_eq_true,↓reduceIte,hashAction,hashReindex_one]
  exact diagonalBlocks_exact _ _ (fun eta => hashedPauli_site_exact (hashApply eta) 0)

def clockLampMatrix (m k : Nat) (isZ : Bool) : Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ :=
  blockMatrix (1:Equiv.Perm (FiniteClock m)) (fun _ => clockLampFibre m k isZ)

theorem clockLampMatrix_unitary (m k : Nat) (isZ : Bool) :
    (clockLampMatrix m k isZ).conjTranspose*clockLampMatrix m k isZ=1 ∧
      clockLampMatrix m k isZ*(clockLampMatrix m k isZ).conjTranspose=1 := by
  have hh := blockMatrix_unitary (β:=FiniteClock m) 1 _ (fun _ => clockLampFibre_unitary m k isZ)
  refine ⟨hh.1.trans ?_,hh.2.trans ?_⟩
  all_goals ext i j; by_cases h : i=j <;> simp [Matrix.one_apply,h]

theorem clockLampMatrix_exact (m k : Nat) :
    clockLampMatrix m k false*clockLampMatrix m k false=1 ∧
      clockLampMatrix m k true*clockLampMatrix m k true=1 ∧
      clockLampMatrix m k false*clockLampMatrix m k true*
        clockLampMatrix m k false*clockLampMatrix m k true= -1 := by
  have hh := diagonalBlocks_exact (β:=FiniteClock m) _ _ (fun _ => clockLampFibre_exact m k)
  refine ⟨hh.1.trans ?_,hh.2.1.trans ?_,hh.2.2.trans ?_⟩
  all_goals ext i j; by_cases h : i=j <;> simp [Matrix.neg_apply,Matrix.one_apply,h]

def clockGenerator (m k : Nat) (j : Published.HashLetter) : Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ :=
  match j.val with
  | 0 => clockHostMatrix m k .p
  | 1 => clockHostMatrix m k .q
  | 2 => clockHostMatrix m k .t
  | 3 => clockHostMatrix m k .d
  | 4 => clockLampMatrix m k false
  | 5 => clockLampMatrix m k true
  | _ => clockHostMatrix m k .i

theorem clockGenerator_unitary (m k : Nat) (j : Published.HashLetter) :
    (clockGenerator m k j).conjTranspose*clockGenerator m k j=1 ∧
      clockGenerator m k j*(clockGenerator m k j).conjTranspose=1 := by
  fin_cases j
  · exact clockHostMatrix_unitary m k .p
  · exact clockHostMatrix_unitary m k .q
  · exact clockHostMatrix_unitary m k .t
  · exact clockHostMatrix_unitary m k .d
  · exact clockLampMatrix_unitary m k false
  · exact clockLampMatrix_unitary m k true
  · exact clockHostMatrix_unitary m k .i

def clockModelHom (m k : Nat) : FreeGroup Published.HashLetter →* Matrix.unitaryGroup (ClockModelIndex m k) ℂ :=
  FreeGroup.lift (fun j => ⟨clockGenerator m k j,clockGenerator_unitary m k j⟩)

theorem clockModelHom_exact (m k : Nat) :
    (clockModelHom m k (FreeGroup.of 4):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)*
      (clockModelHom m k (FreeGroup.of 4):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)=1 ∧
      (clockModelHom m k (FreeGroup.of 5):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)*
      (clockModelHom m k (FreeGroup.of 5):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)=1 ∧
      (clockModelHom m k ((FreeGroup.of 4*FreeGroup.of 5)^2):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)= -1 := by
  simp only [clockModelHom,FreeGroup.lift_apply_of,map_mul,pow_two,Submonoid.coe_mul]
  change clockLampMatrix m k false*clockLampMatrix m k false=1 ∧
    clockLampMatrix m k true*clockLampMatrix m k true=1 ∧
    (clockLampMatrix m k false*clockLampMatrix m k true)*
      (clockLampMatrix m k false*clockLampMatrix m k true)= -1
  simpa only [Matrix.mul_assoc] using clockLampMatrix_exact m k

def clockModelDimension (m k : Nat) : Nat := Fintype.card (ClockModelIndex m k)

theorem clockModelDimension_formula (m k : Nat) :
    clockModelDimension m k=2*(2*m+1)^2*2^(k*(6*m+10))*2^(2^k) := by
  unfold clockModelDimension ClockModelIndex ClockFibre ClockHash ClockRegister
  have hr : 3*(2*m+3)=6*m+9 := by omega
  rw [hr]
  exact hash_space_card m k

theorem clockModelDimension_pos (m k : Nat) : 0<clockModelDimension m k := Fintype.card_pos

def clockModelFiniteHom (m k : Nat) :
    FreeGroup Published.HashLetter →* Matrix.unitaryGroup (Fin (clockModelDimension m k)) ℂ :=
  (AGadget.reindexUnitary (Fintype.equivFin (ClockModelIndex m k))).comp (clockModelHom m k)

theorem clockModelFiniteHom_exact (m k : Nat) :
    (clockModelFiniteHom m k (FreeGroup.of 4):Mat (clockModelDimension m k))*
      (clockModelFiniteHom m k (FreeGroup.of 4):Mat (clockModelDimension m k))=1 ∧
    (clockModelFiniteHom m k (FreeGroup.of 5):Mat (clockModelDimension m k))*
      (clockModelFiniteHom m k (FreeGroup.of 5):Mat (clockModelDimension m k))=1 ∧
    (clockModelFiniteHom m k ((FreeGroup.of 4*FreeGroup.of 5)^2):Mat (clockModelDimension m k))= -1 := by
  have hh := clockModelHom_exact m k
  let T := Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (ClockModelIndex m k))
  change T _*T _=1 ∧ T _*T _=1 ∧ T _= -1
  exact ⟨by rw [←map_mul,hh.1,map_one],by rw [←map_mul,hh.2.1,map_one],by rw [hh.2.2,map_neg,map_one]⟩

end
end Blueprint.AHash

#print axioms Blueprint.AHash.ClockHash
#print axioms Blueprint.AHash.ClockRegister
#print axioms Blueprint.AHash.ClockFibre
#print axioms Blueprint.AHash.ClockModelIndex
#print axioms Blueprint.AHash.clockHostFibre
#print axioms Blueprint.AHash.clockHostFibre_unitary
#print axioms Blueprint.AHash.clockHostFibre_correct
#print axioms Blueprint.AHash.clockHostMatrix
#print axioms Blueprint.AHash.clockHostMatrix_unitary
#print axioms Blueprint.AHash.diagonalBlocks_mul
#print axioms Blueprint.AHash.diagonalBlocks_neg_one
#print axioms Blueprint.AHash.diagonalBlocks_exact
#print axioms Blueprint.AHash.clockLampFibre
#print axioms Blueprint.AHash.clockLampFibre_unitary
#print axioms Blueprint.AHash.clockLampFibre_exact
#print axioms Blueprint.AHash.clockLampMatrix
#print axioms Blueprint.AHash.clockLampMatrix_unitary
#print axioms Blueprint.AHash.clockLampMatrix_exact
#print axioms Blueprint.AHash.clockGenerator
#print axioms Blueprint.AHash.clockGenerator_unitary
#print axioms Blueprint.AHash.clockModelHom
#print axioms Blueprint.AHash.clockModelHom_exact
#print axioms Blueprint.AHash.clockModelDimension
#print axioms Blueprint.AHash.clockModelDimension_formula
#print axioms Blueprint.AHash.clockModelDimension_pos
#print axioms Blueprint.AHash.clockModelFiniteHom
#print axioms Blueprint.AHash.clockModelFiniteHom_exact
