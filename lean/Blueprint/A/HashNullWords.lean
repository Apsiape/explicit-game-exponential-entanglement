import Blueprint.A.HashConcreteCocycle

namespace Blueprint.AHash
noncomputable section
open Companion Concrete
open scoped Classical
set_option maxHeartbeats 600000

def ClockLetterValid (m : Nat) : Letter → FiniteClock m → Prop
  | .host a,c => ClockInside m (clockMove a (clockRead c))
  | _,_ => True

def ClockWordValid (m : Nat) : List Letter → FiniteClock m → Prop
  | [],_ => True
  | a::w,c => ClockWordValid m w c ∧ ClockLetterValid m a (clockWordMove m w c)

theorem clockWordValid_of_safe (m : Nat) (w : List Letter) (c : FiniteClock m)
    (hw : ClockSafe m (letterHosts w) (clockRead c)) : ClockWordValid m w c := by
  induction w with
  | nil => trivial
  | cons a w ih =>
    cases a with
    | host a =>
      have ht := finiteClockTravel_correct m (letterHosts w) c hw.1
      rw [←clockWordMove_hosts] at ht
      exact ⟨ih hw.1,by simpa only [ClockLetterValid,ht] using hw.2⟩
    | x => exact ⟨ih hw,trivial⟩
    | z => exact ⟨ih hw,trivial⟩
    | unit => exact ⟨ih hw,trivial⟩

theorem clockLetterConcrete_finite (m : Nat) (a : Letter) (c : FiniteClock m)
    (hc : ClockLetterValid m a c) (s : Sample) :
    finiteSample (2*m+3) (clockLetterConcrete m a c s)=
      hashGammaAction (clockLetterGamma m a c) (finiteSample (2*m+3) s) := by
  cases a with
  | host a =>
    rw [clockLetterConcrete_host m a c hc]
    change finiteSample (2*m+3) (hostLift (hostEval (hostClockCocycle a (clockRead c))) s)=
      hashGammaAction (clockHostGamma m a c) (finiteSample (2*m+3) s)
    change ClockInside m (clockMove a (clockRead c)) at hc
    simp only [clockHostGamma,dite_eq_left hc]
    exact finiteSample_host _ _ _ s
  | x => rw [clockLetterConcrete_x]; exact finiteSample_x _ s
  | z => rw [clockLetterConcrete_z]; exact finiteSample_z _ s
  | unit => rw [clockLetterConcrete_unit]; exact (hashGammaAction_one _ _).symm

def clockWordConcrete (m : Nat) : List Letter → FiniteClock m → Equiv.Perm Sample
  | [],_ => 1
  | a::w,c => clockLetterConcrete m a (clockWordMove m w c)*clockWordConcrete m w c

theorem clockWordConcrete_eq (m : Nat) (w : List Letter) (c : FiniteClock m) :
    clockWordConcrete m w c=
      (clockSectionLift (clockRead (clockWordMove m w c)))⁻¹*evalLetters w*clockSectionLift (clockRead c) := by
  induction w with
  | nil => change 1=(clockSectionLift (clockRead c))⁻¹*1*clockSectionLift (clockRead c); group
  | cons a w ih =>
    simp only [clockWordConcrete,clockLetterConcrete,clockWordMove,Equiv.Perm.mul_apply,evalLetters,ih]
    group

theorem clockWordConcrete_finite (m : Nat) (w : List Letter) (c : FiniteClock m)
    (hw : ClockWordValid m w c) (s : Sample) :
    finiteSample (2*m+3) (clockWordConcrete m w c s)=
      hashGammaAction (hashGammaProduct (clockWordGammas m w c)) (finiteSample (2*m+3) s) := by
  induction w generalizing s with
  | nil => exact (hashGammaAction_one _ _).symm
  | cons a w ih =>
    rw [clockWordGammas,hashGammaProduct,hashGammaAction_mul,←ih hw.1 s]
    exact clockLetterConcrete_finite m a (clockWordMove m w c) hw.2 (clockWordConcrete m w c s)

theorem clockWordGammas_null (m ell : Nat) (hl : ell≤m) (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell)
    (c : FiniteClock m) (hc : c∈clockInterior m ell hl) :
    hashGammaProduct (clockWordGammas m (w.map hashDecode) c)=hashGammaOne (3*(2*m+3)) := by
  have hsafe := clockInterior_safe m ell hl c hc (letterHosts (w.map hashDecode))
    ((letterHosts_length _).trans (by simpa only [List.length_map] using hL))
  have hvalid := clockWordValid_of_safe m (w.map hashDecode) c hsafe
  have hconcrete : clockWordConcrete m (w.map hashDecode) c=1 := by
    rw [clockWordConcrete_eq,clockWordMove_null_interior m ell hl w hw hL c hc,hashDecode_null w hw]
    group
  apply hashGammaAction_faithful
  intro t
  obtain ⟨s,rfl⟩ := finiteSample_surjective (2*m+3) t
  rw [←clockWordConcrete_finite m (w.map hashDecode) c hvalid s,hconcrete]
  rfl

theorem clockWordFibre_null_row (m k ell : Nat) (hl : ell≤m) (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell)
    (c : FiniteClock m) (hc : c∈clockInterior m ell hl) (eta : ClockHash m k)
    (hinj : Set.InjOn (hashApply eta) (hashProductSites (clockWordGammas m (w.map hashDecode) c) : Set _))
    (v : ClockRegister k) (j : ClockFibre m k) :
    clockWordFibre m k (w.map hashDecode) c (eta,v) j=(1:Matrix (ClockFibre m k) (ClockFibre m k) ℂ) (eta,v) j := by
  exact clockWordFibre_identity_row m k _ c (clockWordGammas_null m ell hl w hw hL c hc) eta hinj v j

end
end Blueprint.AHash

#print axioms Blueprint.AHash.ClockLetterValid
#print axioms Blueprint.AHash.ClockWordValid
#print axioms Blueprint.AHash.clockWordValid_of_safe
#print axioms Blueprint.AHash.clockLetterConcrete_finite
#print axioms Blueprint.AHash.clockWordConcrete
#print axioms Blueprint.AHash.clockWordConcrete_eq
#print axioms Blueprint.AHash.clockWordConcrete_finite
#print axioms Blueprint.AHash.clockWordGammas_null
#print axioms Blueprint.AHash.clockWordFibre_null_row
