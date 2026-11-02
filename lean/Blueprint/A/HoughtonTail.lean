import Blueprint.A.HoughtonCollection

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem johnsonP_perm : johnsonFiniteHom johnsonP=Concrete.pPoint := rfl
theorem johnsonQ_perm : johnsonFiniteHom johnsonQ=Concrete.qPoint := rfl
theorem johnsonAlpha_perm : johnsonFiniteHom johnsonAlpha=
    Concrete.pPoint*Concrete.qPoint*Concrete.pPoint⁻¹*Concrete.qPoint⁻¹ := by
  change pointHom (Published.commutator (FreeGroup.of 1) (FreeGroup.of 2))=_
  simp [Published.commutator,pointHom]

theorem johnson_letter_two (a : Fin 3 × Bool) (h : Nat) (hh : 0<h) :
    (johnsonFiniteHom (johnsonLetter a) (Concrete.Ray.two,h)).1=Concrete.Ray.two ∧
      ((johnsonFiniteHom (johnsonLetter a) (Concrete.Ray.two,h)).2:ℤ)=(h:ℤ)-deltaP a := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hh)
  rcases a with ⟨a,b⟩
  fin_cases a <;> cases b <;> norm_num [johnsonLetter,deltaP,deltaQ,johnsonFiniteHom,johnsonPointHom,pointHom,houghtonS,Published.commutator,Concrete.pPoint,Concrete.qPoint,Concrete.pBackward,Concrete.pForward,Concrete.qBackward,Concrete.qForward,Equiv.Perm.mul_apply,mul_inv_rev]

theorem johnson_letter_three (a : Fin 3 × Bool) (h : Nat) (hh : 0<h) :
    (johnsonFiniteHom (johnsonLetter a) (Concrete.Ray.three,h)).1=Concrete.Ray.three ∧
      ((johnsonFiniteHom (johnsonLetter a) (Concrete.Ray.three,h)).2:ℤ)=(h:ℤ)-deltaQ a := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hh)
  rcases a with ⟨a,b⟩
  fin_cases a <;> cases b <;> norm_num [johnsonLetter,deltaP,deltaQ,johnsonFiniteHom,johnsonPointHom,pointHom,houghtonS,Published.commutator,Concrete.pPoint,Concrete.qPoint,Concrete.pBackward,Concrete.pForward,Concrete.qBackward,Concrete.qForward,Equiv.Perm.mul_apply,mul_inv_rev]

theorem exponent_bounds (w : JohnsonWord) :
    -(w.length:ℤ)≤exponentP w ∧ exponentP w≤w.length ∧
      -(w.length:ℤ)≤exponentQ w ∧ exponentQ w≤w.length := by
  induction w with
  | nil => simp [exponentP,exponentQ]
  | cons a w ih =>
    have hd := delta_bounds a
    rw [exponentP_cons,exponentQ_cons]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

theorem johnson_word_two (w : JohnsonWord) (h : Nat) (hh : w.length<h) :
    (johnsonFiniteHom (FreeGroup.mk w) (Concrete.Ray.two,h)).1=Concrete.Ray.two ∧
      ((johnsonFiniteHom (FreeGroup.mk w) (Concrete.Ray.two,h)).2:ℤ)=(h:ℤ)-exponentP w := by
  induction w generalizing h with
  | nil => simp [exponentP,←FreeGroup.one_eq_mk]
  | cons a w ih =>
    have ht := ih h (by simp only [List.length_cons] at hh; omega)
    let y := johnsonFiniteHom (FreeGroup.mk w) (Concrete.Ray.two,h)
    have hy : y.1=Concrete.Ray.two := ht.1
    have hpos : 0<y.2 := by
      have hb := exponent_bounds w
      dsimp only [y]
      simp only [List.length_cons] at hh
      omega
    have he : y=(Concrete.Ray.two,y.2) := Prod.ext hy rfl
    have hl := johnson_letter_two a y.2 hpos
    rw [johnson_mk_cons,map_mul,Equiv.Perm.mul_apply]
    change (johnsonFiniteHom (johnsonLetter a) y).1=Concrete.Ray.two ∧ ((johnsonFiniteHom (johnsonLetter a) y).2:ℤ)=(h:ℤ)-exponentP (a::w)
    rw [he]
    constructor
    · exact hl.1
    · rw [exponentP_cons]
      calc
        _=(y.2:ℤ)-deltaP a := hl.2
        _=(h:ℤ)-(deltaP a+exponentP w) := by
          rw [show (y.2:ℤ)=(h:ℤ)-exponentP w from ht.2]
          ring

theorem johnson_word_three (w : JohnsonWord) (h : Nat) (hh : w.length<h) :
    (johnsonFiniteHom (FreeGroup.mk w) (Concrete.Ray.three,h)).1=Concrete.Ray.three ∧
      ((johnsonFiniteHom (FreeGroup.mk w) (Concrete.Ray.three,h)).2:ℤ)=(h:ℤ)-exponentQ w := by
  induction w generalizing h with
  | nil => simp [exponentQ,←FreeGroup.one_eq_mk]
  | cons a w ih =>
    have ht := ih h (by simp only [List.length_cons] at hh; omega)
    let y := johnsonFiniteHom (FreeGroup.mk w) (Concrete.Ray.three,h)
    have hy : y.1=Concrete.Ray.three := ht.1
    have hpos : 0<y.2 := by
      have hb := exponent_bounds w
      dsimp only [y]
      simp only [List.length_cons] at hh
      omega
    have he : y=(Concrete.Ray.three,y.2) := Prod.ext hy rfl
    have hl := johnson_letter_three a y.2 hpos
    rw [johnson_mk_cons,map_mul,Equiv.Perm.mul_apply]
    change (johnsonFiniteHom (johnsonLetter a) y).1=Concrete.Ray.three ∧ ((johnsonFiniteHom (johnsonLetter a) y).2:ℤ)=(h:ℤ)-exponentQ (a::w)
    rw [he]
    constructor
    · exact hl.1
    · rw [exponentQ_cons]
      calc
        _=(y.2:ℤ)-deltaQ a := hl.2
        _=(h:ℤ)-(deltaQ a+exponentQ w) := by
          rw [show (y.2:ℤ)=(h:ℤ)-exponentQ w from ht.2]
          ring

theorem null_exponents_zero (w : JohnsonWord) (hw : johnsonFiniteHom (FreeGroup.mk w)=1) :
    exponentP w=0 ∧ exponentQ w=0 := by
  have hp := (johnson_word_two w (w.length+1) (by omega)).2
  have hq := (johnson_word_three w (w.length+1) (by omega)).2
  rw [hw] at hp hq
  change ((w.length+1:Nat):ℤ)=((w.length+1:Nat):ℤ)-exponentP w at hp
  change ((w.length+1:Nat):ℤ)=((w.length+1:Nat):ℤ)-exponentQ w at hq
  omega

/-- The first collection stage now applies to every actual null word of
the concrete Houghton action, with no exponent or filling hypothesis. -/
theorem null_word_collection (n : Nat) (hn : 1≤n) (w : JohnsonWord) (hw : w.length≤n)
    (hnull : johnsonFiniteHom (FreeGroup.mk w)=1) :
    ∃ v : SigmaWord, v.length≤2*n^2 ∧
      (∀ a∈v, 0≤a.1 ∧ a.1≤4*n) ∧
      Close johnsonFiniteRelator
        (collectionState n n*FreeGroup.mk w*(collectionState n n)⁻¹) (sigmaValue v)
        (10*(uniformFarCap (4*n+2)+1)*n^4) := by
  obtain ⟨hp,hq⟩ := null_exponents_zero w hnull
  exact collect_zero_exponent_word n hn w hw hp hq

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.johnsonP_perm
#print axioms Blueprint.HoughtonProof.johnsonQ_perm
#print axioms Blueprint.HoughtonProof.johnsonAlpha_perm
#print axioms Blueprint.HoughtonProof.johnson_letter_two
#print axioms Blueprint.HoughtonProof.johnson_letter_three
#print axioms Blueprint.HoughtonProof.exponent_bounds
#print axioms Blueprint.HoughtonProof.johnson_word_two
#print axioms Blueprint.HoughtonProof.johnson_word_three
#print axioms Blueprint.HoughtonProof.null_exponents_zero
#print axioms Blueprint.HoughtonProof.null_word_collection
