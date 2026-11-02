import Blueprint.A.HoughtonPermutation

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def positiveSigmaWord (v : SigmaWord) : List Nat := v.map (fun a => a.1.toNat)

theorem signed_to_positive_close (v : SigmaWord) (hv : ∀ a∈v, 0≤a.1) :
    Close johnsonFiniteRelator (sigmaValue v) (positiveSigmaValue (positiveSigmaWord v)) v.length := by
  have h := close_product v sigmaLetter (fun a => sigmaZ (a.1.toNat:ℤ)) 1 (by
    intro a ha
    have he : (a.1.toNat:ℤ)=a.1 := by have hh := hv a ha; omega
    rw [he]
    cases hb : a.2
    · simpa only [sigmaLetter,hb,Bool.false_eq_true,↓reduceIte] using sigmaZ_inverse_close a.1
    · simpa only [sigmaLetter,hb,↓reduceIte] using close_weaken (close_refl johnsonFiniteRelator (sigmaZ a.1)) (by omega))
  simpa only [sigmaValue,positiveSigmaValue,positiveSigmaWord,List.map_map,Function.comp_def,Nat.mul_one] using h

theorem collection_total_bound (n F l : Nat) (hn : 1≤n) (hF : 1≤F) (hl : l≤2*n^2) :
    10*F*n^4+(l+l*(4*F*(4*n+1)^2))≤400*n^4*F := by
  have hK : (4*n+1)^2≤25*n^2 := by nlinarith
  have hcost : l*(4*F*(4*n+1)^2)≤(2*n^2)*(4*F*(25*n^2)) :=
    Nat.mul_le_mul hl (Nat.mul_le_mul_left _ hK)
  have hn2 : n^2≤n^4 := by nlinarith [Nat.mul_le_mul_left (n^2) (show 1≤n^2 by nlinarith)]
  have hF' := Nat.mul_le_mul_left (n^4) hF
  nlinarith

/-- Appendix A's collection proposition, including a concrete finite area
witness for every null word; no presentation-completeness input is used. -/
theorem johnson_collection_fills (n : Nat) (hn : 1≤n) :
    Fills johnsonFiniteRelator johnsonFiniteHom n (400*n^4*(uniformFarCap (4*n+2)+1)) := by
  intro w hw hnull
  let M := 4*n+2
  let K := 4*n+1
  let F := uniformFarCap M+1
  obtain ⟨v,hlen,hindices,hcol⟩ := null_word_collection n hn w hw hnull
  have hpos := signed_to_positive_close v (fun a ha => (hindices a ha).1)
  have hwords : ∀ i∈positiveSigmaWord v, i<K := by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    have hh := hindices a ha
    dsimp [K]
    omega
  obtain ⟨c,hc,hnormal⟩ := positive_word_normal_form M (by dsimp [M]; omega) K (by dsimp [K,M]; omega)
    (positiveSigmaWord v) hwords
  have hvnull : johnsonFiniteHom (sigmaValue v)=1 := by
    have hh := (johnson_close_sound hcol).symm
    simpa only [map_mul,map_inv,hnull,mul_one,mul_inv_cancel] using hh
  have hpnull : johnsonFiniteHom (positiveSigmaValue (positiveSigmaWord v))=1 := by
    rw [←johnson_close_sound hpos,hvnull]
  have hnnull : johnsonFiniteHom (coxNormalValue K c)=1 := by
    rw [←johnson_close_sound hnormal,hpnull]
  have hcempty := coxNormal_null K c hc hnnull
  rw [hcempty] at hnormal
  have h := close_to_one.mp (close_trans hcol (close_trans hpos hnormal))
  have he : (positiveSigmaWord v).length=v.length := by simp [positiveSigmaWord]
  rw [he] at h
  have ha := area_conj (collectionState n n)⁻¹ h
  have ha' : FiniteArea.Area johnsonFiniteRelator (FreeGroup.mk w)
      (10*F*n^4+(v.length+v.length*(4*F*K^2))) := by
    convert ha using 1 <;> try rfl
    group
  exact area_weaken ha' (collection_total_bound n F v.length hn (by dsimp [F]; omega) hlen)

theorem johnson_filling_exists (n : Nat) (hn : 1≤n) :
    ∃ C, Fills johnsonFiniteRelator johnsonFiniteHom n C :=
  ⟨_,johnson_collection_fills n hn⟩

theorem houghton_filling_exists (n : Nat) (hn : 1≤n) :
    ∃ C, Fills houghtonFiniteRelator houghtonFiniteHom n C :=
  ⟨_,houghton_fills_of_johnson n _ (johnson_collection_fills n hn)⟩

theorem johnson_dehn_collection (n : Nat) (hn : 1≤n) :
    dehnJ n≤400*n^4*(uniformFarCap (4*n+2)+1) :=
  dehn_le_filling _ _ n _ (johnson_collection_fills n hn)

theorem houghton_dehn_comparison_unconditional (n : Nat) (hn : 1≤n) : dehnH n≤dehnJ n :=
  houghton_dehn_comparison n (johnson_filling_exists n hn)

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.positiveSigmaWord
#print axioms Blueprint.HoughtonProof.signed_to_positive_close
#print axioms Blueprint.HoughtonProof.collection_total_bound
#print axioms Blueprint.HoughtonProof.johnson_collection_fills
#print axioms Blueprint.HoughtonProof.johnson_filling_exists
#print axioms Blueprint.HoughtonProof.houghton_filling_exists
#print axioms Blueprint.HoughtonProof.johnson_dehn_collection
#print axioms Blueprint.HoughtonProof.houghton_dehn_comparison_unconditional
