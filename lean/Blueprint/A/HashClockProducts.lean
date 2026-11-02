import Blueprint.A.HashClockSemantics
import Blueprint.A.HashGammaSemantics

namespace Blueprint.AHash
noncomputable section
open Companion Concrete
open scoped Classical
set_option maxHeartbeats 600000

def clockHostGamma (m : Nat) (a : HostLetter) (c : FiniteClock m) : HashGamma (3*(2*m+3)) :=
  if hc : ClockInside m (clockMove a (clockRead c)) then
    (finiteHostAffine (2*m+3) (hostClockCocycle a (clockRead c))
      (hostClockCocycle_boxFixed a (clockRead c) m
        (clockRead_inside c).1 (clockRead_inside c).2 hc.1 hc.2),0,0,0)
  else hashGammaOne _

def clockLetterGamma (m : Nat) : Letter → FiniteClock m → HashGamma (3*(2*m+3))
  | .host a,c => clockHostGamma m a c
  | .x,_ => (1,0,siteMask 0,0)
  | .z,_ => (1,0,0,siteMask 0)
  | .unit,_ => hashGammaOne _

def clockWordGammas (m : Nat) : List Letter → FiniteClock m → List (HashGamma (3*(2*m+3)))
  | [],_ => []
  | a::w,c => clockLetterGamma m a (clockWordMove m w c)::clockWordGammas m w c

theorem clockLetterGamma_matrix (m k : Nat) (a : Letter) (c : FiniteClock m) :
    hashGammaMatrix (k:=k) (clockLetterGamma m a c)=clockLetterFibre m k a c := by
  cases a with
  | host a =>
    change hashGammaMatrix (k:=k) (clockHostGamma m a c)=clockHostFibre m k a c
    by_cases hc : ClockInside m (clockMove a (clockRead c))
    · simp only [clockHostGamma,clockHostFibre,dite_eq_left hc,hashGammaMatrix]
    · simp only [clockHostGamma,clockHostFibre,dite_eq_right hc,hashGammaMatrix,hashGammaOne,hashAction_one]
  | x => rfl
  | z => rfl
  | unit => exact hashAction_one _ _

theorem clockWordFibre_product (m k : Nat) (w : List Letter) (c : FiniteClock m) :
    clockWordFibre m k w c=((clockWordGammas m w c).map (hashGammaMatrix (k:=k))).prod := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [clockWordFibre,clockWordGammas,List.map_cons,List.prod_cons,clockLetterGamma_matrix,ih]

theorem hashGammaOne_sites (n : Nat) : hashGammaSites (hashGammaOne n)=∅ := by
  ext v
  simp [hashGammaSites,hashGammaOne]

theorem clockLetterGamma_sites_card (m : Nat) (a : Letter) (c : FiniteClock m) :
    (hashGammaSites (clockLetterGamma m a c)).card≤1 := by
  cases a with
  | host a =>
    change (hashGammaSites (clockHostGamma m a c)).card≤1
    by_cases hc : ClockInside m (clockMove a (clockRead c))
    · simp [clockHostGamma,hc,hashGammaSites]
    · simp [clockHostGamma,hc,hashGammaOne_sites]
  | unit => rw [clockLetterGamma,hashGammaOne_sites]; simp
  | x =>
    have he : hashGammaSites (clockLetterGamma m Letter.x c)={0} := by
      ext v; simp [hashGammaSites,clockLetterGamma,siteMask]
    rw [he]; simp
  | z =>
    have he : hashGammaSites (clockLetterGamma m Letter.z c)={0} := by
      ext v; simp [hashGammaSites,clockLetterGamma,siteMask]
    rw [he]; simp

theorem clockWordGammas_length (m : Nat) (w : List Letter) (c : FiniteClock m) :
    (clockWordGammas m w c).length=w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [clockWordGammas,List.length_cons,ih]

theorem clockWordGammas_sites_card (m : Nat) (w : List Letter) (c : FiniteClock m) :
    (hashProductSites (clockWordGammas m w c)).card≤w.length := by
  induction w with
  | nil => simp [clockWordGammas,hashProductSites]
  | cons a w ih =>
    have hh := clockLetterGamma_sites_card m a (clockWordMove m w c)
    have hu := Finset.card_union_le (hashGammaSites (clockLetterGamma m a (clockWordMove m w c)))
      ((hashProductSites (clockWordGammas m w c)).image (clockLetterGamma m a (clockWordMove m w c)).1)
    have hi := Finset.card_image_le (s:=hashProductSites (clockWordGammas m w c))
      (f:=(clockLetterGamma m a (clockWordMove m w c)).1)
    change _≤w.length+1
    change (hashGammaSites (clockLetterGamma m a (clockWordMove m w c)) ∪
      (hashProductSites (clockWordGammas m w c)).image (clockLetterGamma m a (clockWordMove m w c)).1).card≤_
    omega

def letterHosts : List Letter → List HostLetter
  | [] => []
  | .host a::w => a::letterHosts w
  | _::w => letterHosts w

theorem letterHosts_normalForm (w : List Letter) : (normalForm w).host=letterHosts w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [normalForm,prepend,letterHosts,ih]

theorem letterHosts_length (w : List Letter) : (letterHosts w).length≤w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [letterHosts,List.length_cons] <;> omega

theorem clockWordMove_hosts (m : Nat) (w : List Letter) :
    clockWordMove m w=finiteClockTravel m (letterHosts w) := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [clockWordMove,clockLetterMove,letterHosts,finiteClockTravel,ih,one_mul]

theorem hashDecode_null (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) : evalLetters (w.map hashDecode)=1 := by
  have h := congrArg Subtype.val hw
  change wordPermutation true (w.map (fun a => (Published.hashEncode a.1,a.2)))=1 at h
  rw [wordPermutation_eval,List.map_map] at h
  exact h

theorem hashDecode_host_null (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) : hostEval (letterHosts (w.map hashDecode))=1 := by
  have hn : ∀ s, normalAction (normalForm (w.map hashDecode)) s=s := by
    intro s
    rw [←normalForm_sound,hashDecode_null w hw]
    rfl
  rw [←letterHosts_normalForm]
  exact normalAction_host_identity _ hn

theorem clockWordMove_null_interior (m ell : Nat) (hl : ell≤m) (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell)
    (c : FiniteClock m) (hc : c∈clockInterior m ell hl) :
    clockWordMove m (w.map hashDecode) c=c := by
  rw [clockWordMove_hosts]
  apply clockRead_injective m
  rw [finiteClockTravel_correct m _ c (clockInterior_safe m ell hl c hc _
    ((letterHosts_length _).trans (by simpa only [List.length_map] using hL))),
    clockTravel_of_host_identity _ (hashDecode_host_null w hw)]

theorem clockWordFibre_identity_row (m k : Nat) (w : List Letter) (c : FiniteClock m)
    (hprod : hashGammaProduct (clockWordGammas m w c)=hashGammaOne (3*(2*m+3)))
    (eta : ClockHash m k)
    (hinj : Set.InjOn (hashApply eta) (hashProductSites (clockWordGammas m w c) : Set _))
    (v : ClockRegister k) (j : ClockFibre m k) :
    clockWordFibre m k w c (eta,v) j=(1:Matrix (ClockFibre m k) (ClockFibre m k) ℂ) (eta,v) j := by
  rw [clockWordFibre_product]
  exact hashGammaProduct_identity_row _ hprod eta hinj v j

end
end Blueprint.AHash

#print axioms Blueprint.AHash.clockHostGamma
#print axioms Blueprint.AHash.clockLetterGamma
#print axioms Blueprint.AHash.clockWordGammas
#print axioms Blueprint.AHash.clockLetterGamma_matrix
#print axioms Blueprint.AHash.clockWordFibre_product
#print axioms Blueprint.AHash.hashGammaOne_sites
#print axioms Blueprint.AHash.clockLetterGamma_sites_card
#print axioms Blueprint.AHash.clockWordGammas_length
#print axioms Blueprint.AHash.clockWordGammas_sites_card
#print axioms Blueprint.AHash.letterHosts
#print axioms Blueprint.AHash.letterHosts_normalForm
#print axioms Blueprint.AHash.letterHosts_length
#print axioms Blueprint.AHash.clockWordMove_hosts
#print axioms Blueprint.AHash.hashDecode_null
#print axioms Blueprint.AHash.hashDecode_host_null
#print axioms Blueprint.AHash.clockWordMove_null_interior
#print axioms Blueprint.AHash.clockWordFibre_identity_row
