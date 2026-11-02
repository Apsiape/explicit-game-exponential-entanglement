import Blueprint.A.HashClockProducts

namespace Blueprint.AHash
noncomputable section
open Companion Concrete
open scoped Classical
set_option maxHeartbeats 600000

def finiteSite (r : Nat) (v : Fin (3*r) → Bool) : Config :=
  boxEncode ((boxVectorEquiv r).symm v)

theorem finiteSite_injective (r : Nat) : Function.Injective (finiteSite r) :=
  (boxEncode_injective r).comp (boxVectorEquiv r).symm.injective

theorem finiteSite_zero (r : Nat) : finiteSite r 0=∅ := by
  simp [finiteSite,boxEncode]

def finiteSample (r : Nat) (s : Sample) : Bool × ((Fin (3*r) → Bool) → Bool) :=
  (s.1,s.2 ∘ finiteSite r)

theorem finiteSample_surjective (r : Nat) : Function.Surjective (finiteSample r) := by
  rintro ⟨c,q⟩
  refine ⟨(c,fun v => q (boxVectorEquiv r (boxDecode r v))),?_⟩
  apply Prod.ext
  · rfl
  · funext v
    simp only [finiteSample,Function.comp_apply,finiteSite,boxDecode_encode,LinearEquiv.apply_symm_apply]

theorem finiteSample_host (r : Nat) (w : List HostLetter) (hw : BoxFixed r w) (s : Sample) :
    finiteSample r (hostLift (hostEval w) s)=
      hashGammaAction (finiteHostAffine r w hw,0,0,0) (finiteSample r s) := by
  apply Prod.ext
  · simp only [finiteSample,hostLift,Equiv.coe_fn_mk,hashGammaAction,add_zero,registerDot_zero_left]
  · funext v
    have he := finiteHostAffine_encode r (inverseHostWord w) (boxFixed_inverse hw) v
    rw [finiteHostAffine_inverse hw,hostEval_inverse] at he
    change s.2 ((hostEval w).symm (finiteSite r v))=s.2 (finiteSite r ((finiteHostAffine r w hw).symm v))+0
    rw [add_zero]
    exact congrArg s.2 he.symm

theorem finiteSample_x (r : Nat) (s : Sample) :
    finiteSample r (xAt ∅ s)=hashGammaAction (1,0,siteMask 0,0) (finiteSample r s) := by
  apply Prod.ext
  · simp only [finiteSample,xAt,Equiv.coe_fn_mk,hashGammaAction,add_zero,registerDot_zero_left]
  · funext v
    have he : finiteSite r v=∅ ↔ v=0 := by
      rw [←finiteSite_zero r]
      exact (finiteSite_injective r).eq_iff
    change (s.2 (finiteSite r v) ^^ decide (finiteSite r v=∅))=
      s.2 (finiteSite r v)+siteMask 0 v
    simp only [he,siteMask,Bool.add_eq_xor]
    by_cases hv : v=0 <;> cases hq : s.2 (finiteSite r v) <;> simp [hv] <;> rfl

theorem finiteSample_z (r : Nat) (s : Sample) :
    finiteSample r (zAt ∅ s)=hashGammaAction (1,0,0,siteMask 0) (finiteSample r s) := by
  apply Prod.ext
  · change (s.1 ^^ s.2 ∅)=s.1+0+registerDot (siteMask 0) ((finiteSample r s).2 ∘ (1:_ ≃ᵃ[Bool] _).symm)
    rw [registerDot_site,add_zero]
    change (s.1 ^^ s.2 ∅)=s.1+s.2 (finiteSite r 0)
    rw [finiteSite_zero]
    rfl
  · funext v
    change s.2 (finiteSite r v)=s.2 (finiteSite r v)+0
    exact (add_zero _).symm

def hostLiftHom : Equiv.Perm Config →* Equiv.Perm Sample where
  toFun := hostLift
  map_one' := by apply Equiv.ext; rintro ⟨c,q⟩; rfl
  map_mul' := hostLift_mul

theorem clockSection_empty (c : Clock) : hostEval (clockSection c) ∅=∅ := by
  have hp (n : Nat) (a : HostLetter) (ha : hostGenerator a ∅=∅) :
      hostEval (List.replicate n a) ∅=∅ := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [List.replicate_succ,hostEval,Equiv.Perm.mul_apply,ih] using ha
  have hsp (z : ℤ) : hostEval (signedHostPower .p .pinv z) ∅=∅ := by
    cases z <;> apply hp <;> simp [hostGenerator]
  have hsq (z : ℤ) : hostEval (signedHostPower .q .qinv z) ∅=∅ := by
    cases z <;> apply hp <;> simp [hostGenerator]
  simp only [clockSection,hostEval_append,Equiv.Perm.mul_apply]
  rcases c with ⟨u,v,j⟩
  cases j <;> simp only [Bool.false_eq_true,↓reduceIte,hostEval,Equiv.Perm.one_apply,hsp,hsq]
  simp [hostGenerator,hsp,hsq]

theorem hostLift_x_empty (g : Equiv.Perm Config) (hg : g ∅=∅) :
    Commute (hostLift g) (xAt ∅) := by
  apply Equiv.ext
  rintro ⟨c,q⟩
  apply Prod.ext
  · rfl
  · funext v
    change (q (g.symm v) ^^ decide (g.symm v=∅))=(q (g.symm v) ^^ decide (v=∅))
    have he : g.symm v=∅ ↔ v=∅ := by rw [Equiv.symm_apply_eq,hg]
    simp only [he]

theorem hostLift_z_empty (g : Equiv.Perm Config) (hg : g ∅=∅) :
    Commute (hostLift g) (zAt ∅) := by
  apply Equiv.ext
  rintro ⟨c,q⟩
  apply Prod.ext
  · change (c ^^ q ∅)=(c ^^ q (g.symm ∅))
    have he : g.symm ∅=∅ := by
      apply g.injective
      rw [Equiv.apply_symm_apply,hg]
    rw [he]
  · rfl

def clockSectionLift (c : Clock) : Equiv.Perm Sample := hostLiftHom (hostEval (clockSection c))

def clockLetterConcrete (m : Nat) (a : Letter) (c : FiniteClock m) : Equiv.Perm Sample :=
  (clockSectionLift (clockRead (clockLetterMove m a c)))⁻¹*generator a*clockSectionLift (clockRead c)

theorem clockLetterConcrete_host (m : Nat) (a : HostLetter) (c : FiniteClock m)
    (hc : ClockInside m (clockMove a (clockRead c))) :
    clockLetterConcrete m (.host a) c=hostLift (hostEval (hostClockCocycle a (clockRead c))) := by
  simp only [clockLetterConcrete,clockLetterMove,finiteClockMove_correct m a c hc,
    clockSectionLift,hostClockCocycle_eval]
  rfl

theorem clockLetterConcrete_x (m : Nat) (c : FiniteClock m) :
    clockLetterConcrete m .x c=xAt ∅ := by
  change (hostLift (hostEval (clockSection (clockRead c))))⁻¹*xAt ∅*
    hostLift (hostEval (clockSection (clockRead c)))=xAt ∅
  rw [(hostLift_x_empty _ (clockSection_empty _)).inv_left.eq]
  group

theorem clockLetterConcrete_z (m : Nat) (c : FiniteClock m) :
    clockLetterConcrete m .z c=zAt ∅ := by
  change (hostLift (hostEval (clockSection (clockRead c))))⁻¹*zAt ∅*
    hostLift (hostEval (clockSection (clockRead c)))=zAt ∅
  rw [(hostLift_z_empty _ (clockSection_empty _)).inv_left.eq]
  group

theorem clockLetterConcrete_unit (m : Nat) (c : FiniteClock m) : clockLetterConcrete m .unit c=1 := by
  change (clockSectionLift (clockRead c))⁻¹*1*clockSectionLift (clockRead c)=1
  group

end
end Blueprint.AHash

#print axioms Blueprint.AHash.finiteSite
#print axioms Blueprint.AHash.finiteSite_injective
#print axioms Blueprint.AHash.finiteSite_zero
#print axioms Blueprint.AHash.finiteSample
#print axioms Blueprint.AHash.finiteSample_surjective
#print axioms Blueprint.AHash.finiteSample_host
#print axioms Blueprint.AHash.finiteSample_x
#print axioms Blueprint.AHash.finiteSample_z
#print axioms Blueprint.AHash.hostLiftHom
#print axioms Blueprint.AHash.clockSection_empty
#print axioms Blueprint.AHash.hostLift_x_empty
#print axioms Blueprint.AHash.hostLift_z_empty
#print axioms Blueprint.AHash.clockSectionLift
#print axioms Blueprint.AHash.clockLetterConcrete
#print axioms Blueprint.AHash.clockLetterConcrete_host
#print axioms Blueprint.AHash.clockLetterConcrete_x
#print axioms Blueprint.AHash.clockLetterConcrete_z
#print axioms Blueprint.AHash.clockLetterConcrete_unit

