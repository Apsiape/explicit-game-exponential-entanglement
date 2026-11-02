import Blueprint.A.HashFiniteHost

namespace Blueprint.AHash
noncomputable section
open Companion Concrete

theorem boxEncode_injective (r : Nat) : Function.Injective (boxEncode (r:=r)) := by
  intro v u h
  have hh := congrArg (boxDecode r) h
  simpa only [boxDecode_encode] using hh

theorem finiteHostAffine_eq {r : Nat} {u v : List HostLetter} (hu : BoxFixed r u) (hv : BoxFixed r v)
    (he : hostEval u=hostEval v) : finiteHostAffine r u hu=finiteHostAffine r v hv := by
  apply AffineEquiv.ext
  intro x
  apply (boxVectorEquiv r).symm.injective
  apply boxEncode_injective r
  rw [finiteHostAffine_encode,finiteHostAffine_encode,he]

theorem finiteHostAffine_append {r : Nat} {u v : List HostLetter} (hu : BoxFixed r u) (hv : BoxFixed r v) :
    finiteHostAffine r (u++v) (boxFixed_append hu hv)=finiteHostAffine r u hu*finiteHostAffine r v hv := by
  apply AffineEquiv.ext
  intro x
  apply (boxVectorEquiv r).symm.injective
  apply boxEncode_injective r
  change boxEncode ((boxVectorEquiv r).symm (finiteHostAffine r (u++v) _ x))=
    boxEncode ((boxVectorEquiv r).symm (finiteHostAffine r u hu (finiteHostAffine r v hv x)))
  rw [finiteHostAffine_encode,finiteHostAffine_encode,finiteHostAffine_encode,hostEval_append]
  rfl

theorem finiteHostAffine_inverse {r : Nat} {w : List HostLetter} (hw : BoxFixed r w) :
    finiteHostAffine r (inverseHostWord w) (boxFixed_inverse hw)=(finiteHostAffine r w hw).symm := by
  change _=(finiteHostAffine r w hw)⁻¹
  apply (eq_inv_iff_mul_eq_one).mpr
  rw [←finiteHostAffine_append]
  apply finiteHostAffine_identity
  rw [hostEval_append,hostEval_inverse,inv_mul_cancel]

theorem hostClockCocycle_eval (a : HostLetter) (c : Clock) :
    hostEval (hostClockCocycle a c)=
      (hostEval (clockSection (clockMove a c)))⁻¹*hostGenerator a*hostEval (clockSection c) := by
  simp only [hostClockCocycle,hostEval_append,hostEval_inverse,hostEval,mul_one]

theorem hostClockCocycle_inverse_eval (a : HostLetter) (c : Clock) :
    hostEval (hostClockCocycle (inverseHost a) (clockMove a c))=
      (hostEval (hostClockCocycle a c))⁻¹ := by
  rw [hostClockCocycle_eval,hostClockCocycle_eval,clockMove_inverse,hostGenerator_inverse]
  group

theorem hashAction_noLamp_mul {n k : Nat}
    (g h : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) :
    hashAction (k:=k) g 0 0 0*hashAction h 0 0 0=hashAction (g*h) 0 0 0 := by
  simp only [hashAction,hashedPauli,hashPush_zero,registerPauli_one,blockMatrix_mul,
    Matrix.one_mul,hashReindex_mul,←Equiv.Perm.inv_def,mul_inv_rev]

theorem hashAction_noLamp_inverse {n k : Nat}
    (g : (Fin n → Bool) ≃ᵃ[Bool] (Fin n → Bool)) :
    (hashAction (k:=k) g 0 0 0).conjTranspose=hashAction g.symm 0 0 0 := by
  have hmul : hashAction (k:=k) g 0 0 0*hashAction g.symm 0 0 0=1 := by
    rw [hashAction_noLamp_mul]
    simpa only [←AffineEquiv.inv_def,mul_inv_cancel] using hashAction_one n k
  have hu := (hashAction_unitary (k:=k) g 0 0 0).1
  calc
    _=(hashAction g 0 0 0).conjTranspose*(hashAction g 0 0 0*hashAction g.symm 0 0 0) := by rw [hmul,Matrix.mul_one]
    _=hashAction g.symm 0 0 0 := by rw [←Matrix.mul_assoc,hu,Matrix.one_mul]

end
end Blueprint.AHash

#print axioms Blueprint.AHash.boxEncode_injective
#print axioms Blueprint.AHash.finiteHostAffine_eq
#print axioms Blueprint.AHash.finiteHostAffine_append
#print axioms Blueprint.AHash.finiteHostAffine_inverse
#print axioms Blueprint.AHash.hostClockCocycle_eval
#print axioms Blueprint.AHash.hostClockCocycle_inverse_eval
#print axioms Blueprint.AHash.hashAction_noLamp_mul
#print axioms Blueprint.AHash.hashAction_noLamp_inverse
