import Blueprint.A.HashClockUnitary
import Blueprint.A.HashCocycleLaw

namespace Blueprint.AHash
noncomputable section
open Companion Concrete
open scoped Classical
set_option maxHeartbeats 600000

theorem inverseHost_inverse (a : HostLetter) : inverseHost (inverseHost a)=a := by
  cases a <;> rfl

theorem finiteClockMove_valid_inverse (m : Nat) (a : HostLetter) (c : FiniteClock m) :
    ClockInside m (clockMove (inverseHost a) (clockRead (finiteClockMove m a c))) ↔
      ClockInside m (clockMove a (clockRead c)) := by
  constructor
  · intro hc
    have hh := finiteClockMove_correct m (inverseHost a) (finiteClockMove m a c) hc
    rw [finiteClockMove_inverse,Equiv.symm_apply_apply] at hh
    have he := congrArg (clockMove a) hh
    have hi := clockMove_inverse (inverseHost a) (clockRead (finiteClockMove m a c))
    rw [inverseHost_inverse] at hi
    rw [hi] at he
    rw [he]
    exact clockRead_inside _
  · intro hc
    rw [finiteClockMove_correct m a c hc,clockMove_inverse]
    exact clockRead_inside c

theorem clockHostFibre_inverse (m k : Nat) (a : HostLetter) (c : FiniteClock m) :
    clockHostFibre m k (inverseHost a) (finiteClockMove m a c)=
      (clockHostFibre m k a c).conjTranspose := by
  by_cases hc : ClockInside m (clockMove a (clockRead c))
  · have hd := (finiteClockMove_valid_inverse m a c).mpr hc
    rw [clockHostFibre_correct m k a c hc,
      clockHostFibre_correct m k (inverseHost a) (finiteClockMove m a c) hd,
      hashAction_noLamp_inverse]
    congr 1
    have he := hostClockCocycle_inverse_eval a (clockRead c)
    rw [←finiteClockMove_correct m a c hc] at he
    rw [←finiteHostAffine_inverse]
    apply finiteHostAffine_eq
    rw [he,hostEval_inverse]
  · have hd : ¬ClockInside m (clockMove (inverseHost a) (clockRead (finiteClockMove m a c))) :=
      fun h => hc ((finiteClockMove_valid_inverse m a c).mp h)
    simp only [clockHostFibre,dite_eq_right hc,dite_eq_right hd,Matrix.conjTranspose_one]

theorem clockHostMatrix_inverse (m k : Nat) (a : HostLetter) :
    clockHostMatrix m k (inverseHost a)=(clockHostMatrix m k a).conjTranspose := by
  rw [clockHostMatrix,clockHostMatrix,finiteClockMove_inverse,Equiv.symm_symm,blockMatrix_adjoint]
  congr 1
  funext c
  simpa only [Equiv.symm_symm,Equiv.symm_apply_apply] using clockHostFibre_inverse m k a c

theorem unitary_adjoint_of_square {α : Type} [Fintype α] [DecidableEq α]
    (U : Matrix α α ℂ) (hU : U.conjTranspose*U=1) (hsq : U*U=1) : U.conjTranspose=U := by
  calc
    _=U.conjTranspose*(U*U) := by rw [hsq,Matrix.mul_one]
    _=U := by rw [←Matrix.mul_assoc,hU,Matrix.one_mul]

theorem clockLampMatrix_adjoint (m k : Nat) (isZ : Bool) :
    (clockLampMatrix m k isZ).conjTranspose=clockLampMatrix m k isZ := by
  apply unitary_adjoint_of_square _ (clockLampMatrix_unitary m k isZ).1
  cases isZ
  · exact (clockLampMatrix_exact m k).1
  · exact (clockLampMatrix_exact m k).2.1

def clockLetterMove (m : Nat) : Letter → Equiv.Perm (FiniteClock m)
  | .host a => finiteClockMove m a
  | .x | .z | .unit => 1

def clockLetterFibre (m k : Nat) : Letter → FiniteClock m → Matrix (ClockFibre m k) (ClockFibre m k) ℂ
  | .host a,c => clockHostFibre m k a c
  | .x,_ => clockLampFibre m k false
  | .z,_ => clockLampFibre m k true
  | .unit,_ => 1

def clockLetterMatrix (m k : Nat) (a : Letter) : Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ :=
  blockMatrix (clockLetterMove m a).symm (fun c => clockLetterFibre m k a ((clockLetterMove m a).symm c))

theorem clockLetterMatrix_host (m k : Nat) (a : HostLetter) :
    clockLetterMatrix m k (.host a)=clockHostMatrix m k a := rfl

theorem clockLetterMatrix_x (m k : Nat) : clockLetterMatrix m k .x=clockLampMatrix m k false := rfl

theorem clockLetterMatrix_z (m k : Nat) : clockLetterMatrix m k .z=clockLampMatrix m k true := rfl

theorem clockLetterMatrix_unit (m k : Nat) : clockLetterMatrix m k .unit=1 := by
  convert blockMatrix_one (α:=ClockFibre m k) (β:=FiniteClock m) using 1 <;>
    ext i j <;> simp [clockLetterMatrix,clockLetterMove,clockLetterFibre,blockMatrix,Matrix.one_apply,←Equiv.Perm.inv_def] <;> split_ifs <;> simp_all

def hashDecode (a : Published.HashLetter × Bool) : Letter :=
  decode true (Published.hashEncode a.1,a.2)

theorem clockGenerator_signed (m k : Nat) (a : Published.HashLetter × Bool) :
    (if a.2 then clockGenerator m k a.1 else (clockGenerator m k a.1).conjTranspose)=
      clockLetterMatrix m k (hashDecode a) := by
  rcases a with ⟨j,b⟩
  cases b
  · fin_cases j
    · change (clockHostMatrix m k .p).conjTranspose=clockHostMatrix m k .pinv
      exact (clockHostMatrix_inverse m k .p).symm
    · change (clockHostMatrix m k .q).conjTranspose=clockHostMatrix m k .qinv
      exact (clockHostMatrix_inverse m k .q).symm
    · change (clockHostMatrix m k .t).conjTranspose=clockHostMatrix m k .t
      exact (clockHostMatrix_inverse m k .t).symm
    · change (clockHostMatrix m k .d).conjTranspose=clockHostMatrix m k .d
      exact (clockHostMatrix_inverse m k .d).symm
    · change (clockLampMatrix m k false).conjTranspose=clockLampMatrix m k false
      exact clockLampMatrix_adjoint m k false
    · change (clockLampMatrix m k true).conjTranspose=clockLampMatrix m k true
      exact clockLampMatrix_adjoint m k true
    · change (clockHostMatrix m k .i).conjTranspose=clockHostMatrix m k .i
      exact (clockHostMatrix_inverse m k .i).symm
  · fin_cases j <;> rfl

def clockWordMove (m : Nat) : List Letter → Equiv.Perm (FiniteClock m)
  | [] => 1
  | a::w => clockLetterMove m a*clockWordMove m w

def clockWordFibre (m k : Nat) : List Letter → FiniteClock m → Matrix (ClockFibre m k) (ClockFibre m k) ℂ
  | [],_ => 1
  | a::w,c => clockLetterFibre m k a (clockWordMove m w c)*clockWordFibre m k w c

theorem clockLetterMatrices_word (m k : Nat) (w : List Letter) :
    (w.map (clockLetterMatrix m k)).prod=
      blockMatrix (clockWordMove m w).symm (fun c => clockWordFibre m k w ((clockWordMove m w).symm c)) := by
  induction w with
  | nil =>
    convert (blockMatrix_one (α:=ClockFibre m k) (β:=FiniteClock m)).symm using 1 <;>
      ext i j <;> simp [clockWordMove,clockWordFibre,blockMatrix,Matrix.one_apply,←Equiv.Perm.inv_def] <;> split_ifs <;> simp_all
  | cons a w ih =>
    rw [List.map_cons,List.prod_cons,ih,clockLetterMatrix,blockMatrix_mul]
    simp only [clockWordMove,←Equiv.Perm.inv_def,mul_inv_rev]
    congr 1
    funext c
    simp only [clockWordFibre,Equiv.Perm.mul_apply,Equiv.Perm.coe_inv,Equiv.apply_symm_apply]

theorem clockModelHom_word (m k : Nat) (w : Published.HashWord) :
    (clockModelHom m k (FreeGroup.mk w):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)=
      ((w.map hashDecode).map (clockLetterMatrix m k)).prod := by
  induction w with
  | nil => simp [clockModelHom,FreeGroup.lift_mk]
  | cons a w ih =>
    simp only [clockModelHom,FreeGroup.lift_mk,List.map_cons,List.prod_cons,
      Submonoid.coe_mul] at *
    rw [ih]
    congr 1
    rw [←clockGenerator_signed]
    cases a.2 <;> rfl

theorem clockModelHom_block (m k : Nat) (w : Published.HashWord) :
    (clockModelHom m k (FreeGroup.mk w):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ)=
      blockMatrix (clockWordMove m (w.map hashDecode)).symm
        (fun c => clockWordFibre m k (w.map hashDecode) ((clockWordMove m (w.map hashDecode)).symm c)) := by
  rw [clockModelHom_word,clockLetterMatrices_word]

end
end Blueprint.AHash

#print axioms Blueprint.AHash.inverseHost_inverse
#print axioms Blueprint.AHash.finiteClockMove_valid_inverse
#print axioms Blueprint.AHash.clockHostFibre_inverse
#print axioms Blueprint.AHash.clockHostMatrix_inverse
#print axioms Blueprint.AHash.unitary_adjoint_of_square
#print axioms Blueprint.AHash.clockLampMatrix_adjoint
#print axioms Blueprint.AHash.clockLetterMove
#print axioms Blueprint.AHash.clockLetterFibre
#print axioms Blueprint.AHash.clockLetterMatrix
#print axioms Blueprint.AHash.clockLetterMatrix_host
#print axioms Blueprint.AHash.clockLetterMatrix_x
#print axioms Blueprint.AHash.clockLetterMatrix_z
#print axioms Blueprint.AHash.clockLetterMatrix_unit
#print axioms Blueprint.AHash.hashDecode
#print axioms Blueprint.AHash.clockGenerator_signed
#print axioms Blueprint.AHash.clockWordMove
#print axioms Blueprint.AHash.clockWordFibre
#print axioms Blueprint.AHash.clockLetterMatrices_word
#print axioms Blueprint.AHash.clockModelHom_word
#print axioms Blueprint.AHash.clockModelHom_block
