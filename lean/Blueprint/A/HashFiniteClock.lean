import Blueprint.A.HashFiniteHost
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Blueprint.AHash
noncomputable section
open Companion Concrete

abbrev FiniteClock (m : Nat) := Fin (2*m+1) × Fin (2*m+1) × Bool

def clockRead {m : Nat} (c : FiniteClock m) : Clock :=
  ((c.1.val:ℤ)-m,(c.2.1.val:ℤ)-m,c.2.2)

def ClockInside (m : Nat) (c : Clock) : Prop := c.1.natAbs≤m ∧ c.2.1.natAbs≤m

theorem clock_abs_bound (z : ℤ) (m : Nat) : z.natAbs≤m ↔ -(m:ℤ)≤z ∧ z≤m := by
  cases z <;> simp only [Int.natAbs,Int.ofNat_eq_natCast,Int.negSucc_eq] <;> omega

theorem clockRead_inside {m : Nat} (c : FiniteClock m) : ClockInside m (clockRead c) := by
  have h1 := c.1.isLt
  have h2 := c.2.1.isLt
  constructor <;> apply (clock_abs_bound _ _).mpr <;> dsimp [clockRead] <;> omega

theorem clockRead_injective (m : Nat) : Function.Injective (clockRead (m:=m)) := by
  rintro ⟨a,b,j⟩ ⟨u,v,k⟩ hh
  have ha : (a.val:ℤ)-m=(u.val:ℤ)-m := congrArg Prod.fst hh
  have hb : (b.val:ℤ)-m=(v.val:ℤ)-m := congrArg (fun c : Clock => c.2.1) hh
  have hj := congrArg (fun c : Clock => c.2.2) hh
  apply Prod.ext
  · apply Fin.ext; change a.val=u.val; omega
  · apply Prod.ext
    · apply Fin.ext; change b.val=v.val; omega
    · exact hj

def clockSwap (m : Nat) : Equiv.Perm (FiniteClock m) where
  toFun c := (c.2.1,c.1,!c.2.2)
  invFun c := (c.2.1,c.1,!c.2.2)
  left_inv c := by rcases c with ⟨u,v,j⟩; cases j <;> rfl
  right_inv c := by rcases c with ⟨u,v,j⟩; cases j <;> rfl

def finiteClockMove (m : Nat) : HostLetter → Equiv.Perm (FiniteClock m)
  | .p => Equiv.prodCongr (finRotate (2*m+1)) (Equiv.refl _)
  | .pinv => Equiv.prodCongr (finRotate (2*m+1)).symm (Equiv.refl _)
  | .q => Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (finRotate (2*m+1)) (Equiv.refl _))
  | .qinv => Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (finRotate (2*m+1)).symm (Equiv.refl _))
  | .i => clockSwap m
  | .t | .d => 1

theorem finiteClockMove_inverse (m : Nat) (a : HostLetter) :
    finiteClockMove m (inverseHost a)=(finiteClockMove m a).symm := by
  cases a <;> rfl

theorem finiteClockMove_correct (m : Nat) (a : HostLetter) (c : FiniteClock m)
    (hc : ClockInside m (clockMove a (clockRead c))) :
    clockRead (finiteClockMove m a c)=clockMove a (clockRead c) := by
  rcases c with ⟨u,v,j⟩
  have hu := u.isLt
  have hv := v.isLt
  have h1 := (clock_abs_bound _ _).mp hc.1
  have h2 := (clock_abs_bound _ _).mp hc.2
  cases a
  · have hn : u≠Fin.last (2*m) := by
      intro he
      have := congrArg Fin.val he
      dsimp [clockMove,clockRead] at h1
      simp only [Fin.val_last] at this
      omega
    have hh := coe_finRotate_of_ne_last hn
    apply Prod.ext
    · change (((finRotate (2*m+1) u).val:ℤ)-m)=((u.val:ℤ)-m)+1
      change (finRotate (2*m+1) u).val=u.val+1 at hh
      omega
    · rfl
  · let : NeZero (2*m+1) := ⟨by omega⟩
    have hn : u≠0 := by
      intro he
      have := congrArg Fin.val he
      dsimp [clockMove,clockRead] at h1
      simp only [Fin.val_zero] at this
      omega
    have hh := coe_finRotate_symm_of_ne_zero hn
    apply Prod.ext
    · change ((((finRotate (2*m+1)).symm u).val:ℤ)-m)=((u.val:ℤ)-m)-1
      change ((finRotate (2*m+1)).symm u).val=u.val-1 at hh
      have hz : 0<u.val := Nat.pos_of_ne_zero (fun h => hn (Fin.ext h))
      omega
    · rfl
  · have hn : v≠Fin.last (2*m) := by
      intro he
      have := congrArg Fin.val he
      dsimp [clockMove,clockRead] at h2
      simp only [Fin.val_last] at this
      omega
    have hh := coe_finRotate_of_ne_last hn
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change (((finRotate (2*m+1) v).val:ℤ)-m)=((v.val:ℤ)-m)+1
        change (finRotate (2*m+1) v).val=v.val+1 at hh
        omega
      · rfl
  · let : NeZero (2*m+1) := ⟨by omega⟩
    have hn : v≠0 := by
      intro he
      have := congrArg Fin.val he
      dsimp [clockMove,clockRead] at h2
      simp only [Fin.val_zero] at this
      omega
    have hh := coe_finRotate_symm_of_ne_zero hn
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change ((((finRotate (2*m+1)).symm v).val:ℤ)-m)=((v.val:ℤ)-m)-1
        change ((finRotate (2*m+1)).symm v).val=v.val-1 at hh
        have hz : 0<v.val := Nat.pos_of_ne_zero (fun h => hn (Fin.ext h))
        omega
      · rfl
  · rfl
  · rfl
  · rfl

def finiteClockTravel (m : Nat) : List HostLetter → Equiv.Perm (FiniteClock m)
  | [] => 1
  | a::w => finiteClockMove m a*finiteClockTravel m w

def ClockSafe (m : Nat) : List HostLetter → Clock → Prop
  | [],c => ClockInside m c
  | a::w,c => ClockSafe m w c ∧ ClockInside m (clockMove a (clockTravel w c))

theorem finiteClockTravel_correct (m : Nat) (w : List HostLetter) (c : FiniteClock m)
    (hw : ClockSafe m w (clockRead c)) :
    clockRead (finiteClockTravel m w c)=clockTravel w (clockRead c) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change clockRead (finiteClockMove m a (finiteClockTravel m w c))=_
    have hh := ih hw.1
    rw [finiteClockMove_correct m a _ (by simpa only [hh] using hw.2),hh]
    rfl

theorem clockInside_step (a : HostLetter) (n : Nat) (c : Clock) (hc : ClockInside n c) :
    ClockInside (n+1) (clockMove a c) := by
  have h1 := (clock_abs_bound _ _).mp hc.1
  have h2 := (clock_abs_bound _ _).mp hc.2
  rcases c with ⟨u,v,j⟩
  change -(n:ℤ)≤u ∧ u≤n at h1
  change -(n:ℤ)≤v ∧ v≤n at h2
  cases a <;> constructor <;> apply (clock_abs_bound _ _).mpr <;> dsimp [clockMove] <;> omega

theorem clockInside_mono {m n : Nat} {c : Clock} (hc : ClockInside m c) (hmn : m≤n) :
    ClockInside n c := ⟨hc.1.trans hmn,hc.2.trans hmn⟩

theorem clockTravel_inside (w : List HostLetter) (n : Nat) (c : Clock) (hc : ClockInside n c) :
    ClockInside (n+w.length) (clockTravel w c) := by
  induction w with
  | nil => simpa only [clockTravel,List.length_nil,Nat.add_zero] using hc
  | cons a w ih =>
    have hh := clockInside_step a (n+w.length) (clockTravel w c) ih
    simpa only [clockTravel,List.length_cons,Nat.add_assoc] using hh

theorem clockSafe_of_interior (w : List HostLetter) (n m : Nat) (c : Clock)
    (hc : ClockInside n c) (hm : n+w.length≤m) : ClockSafe m w c := by
  induction w with
  | nil => exact clockInside_mono hc (by simpa using hm)
  | cons a w ih =>
    have hlen : n+w.length≤m := by simp only [List.length_cons] at hm; omega
    refine ⟨ih hlen,?_⟩
    exact clockInside_mono (clockTravel_inside (a::w) n c hc) hm

theorem finiteClockTravel_identity (m : Nat) (w : List HostLetter) (c : FiniteClock m)
    (hw : ClockSafe m w (clockRead c)) (he : hostEval w=1) : finiteClockTravel m w c=c := by
  apply clockRead_injective m
  rw [finiteClockTravel_correct m w c hw,clockTravel_of_host_identity w he]

theorem finiteClock_card (m : Nat) : Fintype.card (FiniteClock m)=2*(2*m+1)^2 := by
  simp only [FiniteClock,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

end
end Blueprint.AHash

#print axioms Blueprint.AHash.FiniteClock
#print axioms Blueprint.AHash.clockRead
#print axioms Blueprint.AHash.ClockInside
#print axioms Blueprint.AHash.clock_abs_bound
#print axioms Blueprint.AHash.clockRead_inside
#print axioms Blueprint.AHash.clockRead_injective
#print axioms Blueprint.AHash.clockSwap
#print axioms Blueprint.AHash.finiteClockMove
#print axioms Blueprint.AHash.finiteClockMove_inverse
#print axioms Blueprint.AHash.finiteClockMove_correct
#print axioms Blueprint.AHash.finiteClockTravel
#print axioms Blueprint.AHash.ClockSafe
#print axioms Blueprint.AHash.finiteClockTravel_correct
#print axioms Blueprint.AHash.clockInside_step
#print axioms Blueprint.AHash.clockInside_mono
#print axioms Blueprint.AHash.clockTravel_inside
#print axioms Blueprint.AHash.clockSafe_of_interior
#print axioms Blueprint.AHash.finiteClockTravel_identity
#print axioms Blueprint.AHash.finiteClock_card
