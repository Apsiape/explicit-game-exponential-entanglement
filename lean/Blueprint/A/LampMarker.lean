import Blueprint.A.LampWordBounds

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic ASector PairProof Published AWordAreaProof
open scoped BigOperators ComplexOrder MatrixOrder

theorem lampJ_alphabet : ∀ a∈lampJ, 1≤a.1 ∧ a.1≤6 := by
  intro a ha
  simp only [lampJ,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> omega

theorem lampJ_rounding {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (hm : sourceModel U s e) :
    let W := wordEval U lampJ
    let J := roundUnitary W
    IsInvolution J ∧ hs ((J-W)*s.xi)≤e ∧ hs (comm J s.xi)≤6*e := by
  dsimp only
  let W := wordEval U lampJ
  have hW : IsUnitary W := wordEval_unitary U hm.1 lampJ
  have hsq : hs ((W*W-1)*s.xi)≤e := by
    have hh := hm.2.1 (lampJ++lampJ) (by decide +kernel)
    simpa only [TransferProof.wordEval_append] using hh
  have hr := ReturnProof.rounding_weighted_bound W hW s.xi
  have hc := ReturnProof.rounding_commutator_bound W s.xi hW s.xi_positive.isHermitian
  have hcw := source_word_comm U s e hm lampJ lampJ_alphabet
  norm_num only [lampJ,List.length_cons,List.length_nil,Nat.cast_ofNat] at hcw
  change hs (comm W s.xi)≤4*e at hcw
  refine ⟨ReturnProof.roundUnitary_involution W,hr.trans hsq,?_⟩
  change hs (comm (roundUnitary W) s.xi)≤6*e
  simp only [hs_eq_hsNorm] at *
  linarith

theorem transported_pair_product {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) (v : Word) :
    wordEval U (transportLamp v 5)*wordEval U (transportLamp v 6)*
      wordEval U (transportLamp v 5)*wordEval U (transportLamp v 6)=
    wordEval U v*wordEval U lampJ*(wordEval U v).conjTranspose := by
  let G := wordEval U v
  have hG : IsUnitary G := wordEval_unitary U hU v
  have hmul (A B : Mat d) : (G*A*G.conjTranspose)*(G*B*G.conjTranspose)=G*(A*B)*G.conjTranspose := by
    calc
      _=G*A*(G.conjTranspose*G)*B*G.conjTranspose := by simp only [Matrix.mul_assoc]
      _=_ := by simp only [hG.1,Matrix.mul_one,Matrix.mul_assoc]
  rw [transport_eval U hU v 5,transport_eval U hU v 6]
  change ((G*U 5*G.conjTranspose)*(G*U 6*G.conjTranspose))*(G*U 5*G.conjTranspose)*
    (G*U 6*G.conjTranspose)=G*wordEval U lampJ*G.conjTranspose
  rw [hmul,hmul,hmul]
  simp only [lampJ,wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    ↓reduceIte,Matrix.mul_one,Matrix.mul_assoc]

theorem lamp_marker_bound (hlit : ConjugatorLengths) {d : Nat}
    (U : Nat → Mat d) (s : State d) (e : ℝ) (he : 0≤e) (hm : sourceModel U s e)
    (v : Word) (hv : ∀ a∈v, 1≤a.1 ∧ a.1≤6) (ell : Nat) (hell : 63≤ell) (hlen : v.length≤ell)
    (harea : FiniteArea.Area sourceRelator (FreeGroup.mk (commWord v lampJ)) (4*v.length))
    (X Z : Mat d) (hX : IsUnitary X) (hZ : IsUnitary Z)
    (hXA : hs ((X-wordEval U (transportLamp v 5))*s.xi)≤(2*ell+1)*e)
    (hZB : hs ((Z-wordEval U (transportLamp v 6))*s.xi)≤(2*ell+1)*e) :
    hs ((X*Z*X*Z-roundUnitary (wordEval U lampJ))*s.xi)≤10000*(ell:ℝ)^2*e := by
  let A := wordEval U (transportLamp v 5)
  let B := wordEval U (transportLamp v 6)
  let W := wordEval U lampJ
  let Q := wordEval U (commWord v lampJ)
  have hA : IsUnitary A := wordEval_unitary U hm.1 _
  have hB : IsUnitary B := wordEval_unitary U hm.1 _
  have hW : IsUnitary W := wordEval_unitary U hm.1 _
  have hQ : IsUnitary Q := wordEval_unitary U hm.1 _
  have hlenQ : (commWord v lampJ).length≤2*ell+8 := by
    simp only [commWord,List.length_append,FreeGroup.invRev_length,lampJ,List.length_cons,List.length_nil]
    omega
  have hbound := source_area_estimate hlit U s e he hm (commWord v lampJ)
    (comm_letters v lampJ (fun j => 1≤j ∧ j≤6) hv lampJ_alphabet) (4*ell)
    (area_weaken harea (Nat.mul_le_mul_left 4 hlen))
  have hcost : (4*ell)*(1+2*((commWord v lampJ).length+30*(4*ell)))≤2000*ell^2 := by
    have hh : 1+2*((commWord v lampJ).length+30*(4*ell))≤244*ell+17 := by omega
    have hh' := Nat.mul_le_mul_left (4*ell) hh
    nlinarith [Nat.mul_le_mul_left ell (show 1≤ell by omega)]
  have hQD : hs ((Q-1)*s.xi)≤2000*(ell:ℝ)^2*e := hbound.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcost) he)
  have hcW := source_word_comm U s e hm lampJ lampJ_alphabet
  norm_num only [lampJ,List.length_cons,List.length_nil,Nat.cast_ofNat] at hcW
  change hs (comm W s.xi)≤4*e at hcW
  have hmove := ReturnProof.unitary_difference_right_transport Q 1 W s.xi hQ (by simp [IsUnitary]) hW
  have heq : (Q-1)*W=A*B*A*B-W := by
    rw [transported_pair_product U hm.1 v]
    dsimp only [Q]
    rw [word_comm_eval U hm.1]
    change (wordEval U v*W*(wordEval U v).conjTranspose*W.conjTranspose-1)*W=_
    calc
      _=(wordEval U v*W*(wordEval U v).conjTranspose)*(W.conjTranspose*W)-W := by
        simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc]
      _=_ := by rw [hW.1,Matrix.mul_one]
  rw [heq] at hmove
  have hAB : hs ((A*B*A*B-W)*s.xi)≤2000*(ell:ℝ)^2*e+8*e := by
    simp only [hs_eq_hsNorm] at *
    linarith
  have hc (j : Nat) (hj : j∈[5,6]) : hs (comm (wordEval U (transportLamp v j)) s.xi)≤(2*ell+1)*e := by
    have hh := source_word_comm U s e hm (transportLamp v j)
      (transport_letters v j (fun k => 1≤k ∧ k≤6) hv (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega))
    have hl : (transportLamp v j).length≤2*ell+1 := by
      simp only [transportLamp,List.length_append,List.length_cons,List.length_nil,FreeGroup.invRev_length]
      omega
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) he)
  let L : List (Mat d × Mat d) := [(X,A),(Z,B),(X,A),(Z,B)]
  have hrep := ReturnProof.unitary_list_replacement L s.xi ((2*ell+1)*e)
    (by intro p hp; simp only [L,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl <;> first | exact ⟨hX,hA⟩ | exact ⟨hZ,hB⟩)
    (by intro p hp; simp only [L,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl <;> first | exact hXA | exact hZB)
    (by intro p hp; simp only [L,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl <;> first | exact hc 5 (by simp) | exact hc 6 (by simp))
  have hrep' : hs ((X*Z*X*Z-A*B*A*B)*s.xi)≤16*((2*ell+1)*e) := by
    norm_num [L,Matrix.mul_assoc,hs_eq_hsNorm] at hrep
    simpa only [hs_eq_hsNorm,Matrix.mul_assoc] using hrep
  have hJ := (lampJ_rounding U s e hm).2.1
  have hsum1 := hsNorm_add_le ((X*Z*X*Z-A*B*A*B)*s.xi) ((A*B*A*B-W)*s.xi)
  have hsum2 := CountProof.hs_sub_le ((X*Z*X*Z-W)*s.xi) ((roundUnitary W-W)*s.xi)
  have he1 : (X*Z*X*Z-A*B*A*B)*s.xi+(A*B*A*B-W)*s.xi=(X*Z*X*Z-W)*s.xi := by
    simp only [Matrix.sub_mul]; abel
  have he2 : (X*Z*X*Z-W)*s.xi-(roundUnitary W-W)*s.xi=(X*Z*X*Z-roundUnitary W)*s.xi := by
    simp only [Matrix.sub_mul]; abel
  rw [he1] at hsum1
  rw [he2] at hsum2
  have hnum : (16:ℝ)*(2*ell+1)+2000*(ell:ℝ)^2+9≤10000*(ell:ℝ)^2 := by
    have hE : (63:ℝ)≤ell := by exact_mod_cast hell
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hnum he
  simp only [hs_eq_hsNorm] at *
  linarith

end
end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.lampJ_alphabet
#print axioms Blueprint.ASectorProof.lampJ_rounding
#print axioms Blueprint.ASectorProof.transported_pair_product
#print axioms Blueprint.ASectorProof.lamp_marker_bound
