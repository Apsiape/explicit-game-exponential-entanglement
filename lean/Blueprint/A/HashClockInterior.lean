import Blueprint.A.HashFiniteClock

namespace Blueprint.AHash
noncomputable section
open Companion Concrete

def clockInteriorEmbed (m ell : Nat) (hl : ell≤m) : FiniteClock (m-ell) ↪ FiniteClock m where
  toFun c := (⟨c.1.val+ell,by have := c.1.isLt; omega⟩,
    ⟨c.2.1.val+ell,by have := c.2.1.isLt; omega⟩,c.2.2)
  inj' := by
    rintro ⟨a,b,j⟩ ⟨u,v,k⟩ hh
    have ha : a.val+ell=u.val+ell := congrArg (fun c : FiniteClock m => c.1.val) hh
    have hb : b.val+ell=v.val+ell := congrArg (fun c : FiniteClock m => c.2.1.val) hh
    have hj : j=k := congrArg (fun c : FiniteClock m => c.2.2) hh
    apply Prod.ext
    · apply Fin.ext; change a.val=u.val; omega
    · apply Prod.ext
      · apply Fin.ext; change b.val=v.val; omega
      · exact hj

def clockInterior (m ell : Nat) (hl : ell≤m) : Finset (FiniteClock m) :=
  Finset.univ.map (clockInteriorEmbed m ell hl)

theorem clockInterior_card (m ell : Nat) (hl : ell≤m) :
    (clockInterior m ell hl).card=2*(2*(m-ell)+1)^2 := by
  rw [clockInterior,Finset.card_map,Finset.card_univ,finiteClock_card]

theorem clockInterior_read (m ell : Nat) (hl : ell≤m) (c : FiniteClock (m-ell)) :
    clockRead (clockInteriorEmbed m ell hl c)=clockRead c := by
  apply Prod.ext
  · change ((c.1.val+ell:Nat):ℤ)-m=(c.1.val:ℤ)-(m-ell:Nat)
    omega
  · apply Prod.ext
    · change ((c.2.1.val+ell:Nat):ℤ)-m=(c.2.1.val:ℤ)-(m-ell:Nat)
      omega
    · rfl

theorem clockInterior_safe (m ell : Nat) (hl : ell≤m) (c : FiniteClock m)
    (hc : c∈clockInterior m ell hl) (w : List HostLetter) (hw : w.length≤ell) :
    ClockSafe m w (clockRead c) := by
  obtain ⟨d,_,rfl⟩ := Finset.mem_map.mp hc
  rw [clockInterior_read]
  exact clockSafe_of_interior w (m-ell) m (clockRead d) (clockRead_inside d) (by omega)

theorem clockInterior_boundary (m ell : Nat) (hm : 1≤m) (hl : ell≤m) :
    1-((clockInterior m ell hl).card:ℝ)/Fintype.card (FiniteClock m)≤4*ell/(2*m+1) := by
  rw [clockInterior_card,finiteClock_card]
  have he : ((2*(2*(m-ell)+1)^2:Nat):ℝ)/((2*(2*m+1)^2:Nat):ℝ)=
      (2*(m:ℝ)-2*ell+1)^2/(2*m+1)^2 := by
    push_cast
    rw [Nat.cast_sub hl]
    field_simp
    <;> ring
  rw [he]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using clock_boundary m ell hm hl

end
end Blueprint.AHash

#print axioms Blueprint.AHash.clockInteriorEmbed
#print axioms Blueprint.AHash.clockInterior
#print axioms Blueprint.AHash.clockInterior_card
#print axioms Blueprint.AHash.clockInterior_read
#print axioms Blueprint.AHash.clockInterior_safe
#print axioms Blueprint.AHash.clockInterior_boundary
