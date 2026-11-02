import Blueprint.A.HoughtonCollectionLetters

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000

/-- Collection with explicit exponent slack. Every emitted transposition
lies on ray one at an index between zero and 4n; all costs are actual cells. -/
theorem collect_bounded_word (n : Nat) (hn : 1≤n) (w : JohnsonWord) (m l : ℤ)
    (hmlo : (w.length:ℤ)≤m) (hmhi : m+w.length≤2*n)
    (hllo : (w.length:ℤ)≤l) (hlhi : l+w.length≤2*n) :
    ∃ v : SigmaWord, v.length≤2*n*w.length ∧
      (∀ a∈v, 0≤a.1 ∧ a.1≤4*n) ∧
      Close johnsonFiniteRelator (collectionState m l*FreeGroup.mk w)
        (sigmaValue v*collectionState (m+exponentP w) (l+exponentQ w))
        (w.length*(10*(uniformFarCap (4*n+2)+1)*n^3)) := by
  induction w generalizing m l with
  | nil =>
    refine ⟨[],by simp,by simp,?_⟩
    simpa [sigmaValue,exponentP,exponentQ,←FreeGroup.one_eq_mk] using close_refl johnsonFiniteRelator (collectionState m l)
  | cons a w ih =>
    have hd := delta_bounds a
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hmlo hmhi hllo hlhi
    have hlcast : (l.toNat:ℤ)=l := by omega
    have hln : l.toNat≤2*n := by omega
    let u := collectionLetterWord m l.toNat a
    have huLen : u.length≤2*n := collectionLetter_length m l.toNat a n hn hln
    have huIndices : ∀ x∈u, 0≤x.1 ∧ x.1≤4*n :=
      collectionLetter_indices m l.toNat a n (by omega) (by omega) hln
    have hu : Close johnsonFiniteRelator (collectionState m l*johnsonLetter a)
        (sigmaValue u*collectionState (m+deltaP a) (l+deltaQ a))
        (10*(uniformFarCap (4*n+2)+1)*n^3) := by
      simpa only [hlcast] using collect_letter n hn m l.toNat hln a
    obtain ⟨v,hvLen,hvIndices,hv⟩ := ih (m+deltaP a) (l+deltaQ a)
      (by omega) (by omega) (by omega) (by omega)
    have h1 := close_right (FreeGroup.mk w) hu
    have h2 := close_left (sigmaValue u) hv
    have h := close_trans h1 (by simpa only [mul_assoc] using h2)
    refine ⟨u++v,?_,?_,?_⟩
    · simp only [List.length_append,List.length_cons]
      nlinarith
    · intro x hx
      rcases List.mem_append.mp hx with hx|hx
      · exact huIndices x hx
      · exact hvIndices x hx
    · convert h using 1
      · rw [johnson_mk_cons,mul_assoc]
      · simp only [sigmaValue_append,exponentP_cons,exponentQ_cons,mul_assoc,add_assoc]
      · simp only [List.length_cons]
        ring

theorem collect_zero_exponent_word (n : Nat) (hn : 1≤n) (w : JohnsonWord) (hw : w.length≤n)
    (hp : exponentP w=0) (hq : exponentQ w=0) :
    ∃ v : SigmaWord, v.length≤2*n^2 ∧
      (∀ a∈v, 0≤a.1 ∧ a.1≤4*n) ∧
      Close johnsonFiniteRelator
        (collectionState n n*FreeGroup.mk w*(collectionState n n)⁻¹) (sigmaValue v)
        (10*(uniformFarCap (4*n+2)+1)*n^4) := by
  obtain ⟨v,hlen,hi,hclose⟩ := collect_bounded_word n hn w n n (by omega) (by omega) (by omega) (by omega)
  refine ⟨v,by nlinarith,hi,?_⟩
  have h := close_right (collectionState n n)⁻¹ hclose
  simp only [hp,hq,add_zero,mul_inv_cancel_right] at h
  apply close_weaken h
  calc
    w.length*(10*(uniformFarCap (4*n+2)+1)*n^3)
      ≤ n*(10*(uniformFarCap (4*n+2)+1)*n^3) := Nat.mul_le_mul_right _ hw
    _ = _ := by ring

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.collect_bounded_word
#print axioms Blueprint.HoughtonProof.collect_zero_exponent_word
