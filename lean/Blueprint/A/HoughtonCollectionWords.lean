import Blueprint.A.HoughtonUniform

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
open scoped BigOperators
set_option maxHeartbeats 1000000

abbrev SigmaWord := List (ℤ × Bool)

def sigmaLetter (a : ℤ × Bool) : FreeGroup (Fin 3) := if a.2 then sigmaZ a.1 else (sigmaZ a.1)⁻¹
def sigmaValue (v : SigmaWord) : FreeGroup (Fin 3) := (v.map sigmaLetter).prod

def sigmaDescendingWord (m : ℤ) (b : Bool) : Nat → SigmaWord
  | 0 => []
  | l+1 => (m+l,b)::sigmaDescendingWord m b l

def sigmaInverseWord (v : SigmaWord) : SigmaWord := (v.map (fun a => (a.1,!a.2))).reverse

theorem sigmaValue_append (v w : SigmaWord) : sigmaValue (v++w)=sigmaValue v*sigmaValue w := by
  simp only [sigmaValue,List.map_append,List.prod_append]

theorem sigmaValue_inverse (v : SigmaWord) : sigmaValue (sigmaInverseWord v)=(sigmaValue v)⁻¹ := by
  have hf (a : ℤ × Bool) : sigmaLetter (a.1,!a.2)=(sigmaLetter a)⁻¹ := by
    cases hb : a.2 <;> simp [sigmaLetter,hb]
  simp only [sigmaInverseWord,sigmaValue,List.map_reverse,List.map_map,Function.comp_def,hf]
  calc
    _=((v.map sigmaLetter).map (fun x => x⁻¹)).reverse.prod := by rw [List.map_map]; rfl
    _=(v.map sigmaLetter).prod⁻¹ := (List.prod_inv_reverse _).symm

theorem sigmaInverseWord_length (v : SigmaWord) : (sigmaInverseWord v).length=v.length := by
  simp [sigmaInverseWord]

theorem sigmaInverseWord_indices (v : SigmaWord) (L U : ℤ)
    (hv : ∀ a∈v, L≤a.1 ∧ a.1≤U) : ∀ a∈sigmaInverseWord v, L≤a.1 ∧ a.1≤U := by
  intro a ha
  obtain ⟨b,hb,he⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  obtain rfl := he
  exact hv b hb

theorem sigmaDescendingWord_length (m : ℤ) (b : Bool) (l : Nat) :
    (sigmaDescendingWord m b l).length=l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [sigmaDescendingWord,List.length_cons,ih]

theorem sigmaDescendingWord_indices (m : ℤ) (b : Bool) (l : Nat) :
    ∀ a∈sigmaDescendingWord m b l, m≤a.1 ∧ a.1<m+l := by
  induction l with
  | zero => simp [sigmaDescendingWord]
  | succ l ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · simp only [Nat.cast_add,Nat.cast_one]; omega
    · obtain ⟨hl,hu⟩ := ih a ha
      simp only [Nat.cast_add,Nat.cast_one]; omega

theorem sigmaDescendingWord_value (m : ℤ) (l : Nat) :
    sigmaValue (sigmaDescendingWord m true l)=sigmaDescending m l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [sigmaDescendingWord,sigmaValue,List.map_cons,List.prod_cons,
      sigmaLetter,↓reduceIte,sigmaDescending,←ih]

def qInverseDescending : Nat → FreeGroup (Fin 3)
  | 0 => 1
  | l+1 => (qSigma l)⁻¹*qInverseDescending l

theorem qConjP_expansion (l : Nat) :
    Close johnsonFiniteRelator (johnsonQ^l*johnsonP*(johnsonQ^l)⁻¹)
      (qInverseDescending l*johnsonP) l := by
  induction l with
  | zero => simpa [qInverseDescending] using close_refl johnsonFiniteRelator johnsonP
  | succ l ih =>
    have hc : Close johnsonFiniteRelator (johnsonQ^(l+1)*johnsonP*(johnsonQ^(l+1))⁻¹)
        ((qSigma l)⁻¹*(johnsonQ^l*johnsonP*(johnsonQ^l)⁻¹)) 1 := by
      convert close_conj (johnsonQ^l) johnson_qp_close using 1
      · rw [pow_succ]; group
      · dsimp [qSigma]; group
    have h := close_trans hc (close_left (qSigma l)⁻¹ ih)
    simpa only [qInverseDescending,mul_assoc,Nat.add_comm] using h

theorem transferBound_constant_le (A l : Nat) : transferBound (fun _ => A) l≤(A+1)*l^2 := by
  induction l with
  | zero => simp [transferBound]
  | succ l ih =>
    have he : etaBound (fun _ => A) l=2*l+1+l*A := by simp [etaBound]
    rw [transferBound,Finset.sum_range_succ,he]
    change transferBound (fun _ => A) l+(2*l+1+l*A)≤(A+1)*(l+1)^2
    nlinarith

theorem qSigma_uniform_close (M : Nat) (hM : 2≤M) (l : Nat) (hl : l≤M) :
    Close johnsonFiniteRelator (qSigma l) (sigmaZ l) ((uniformFarCap M+1)*l^2) := by
  apply close_weaken (qSigma_close l (fun _ => uniformFarCap M) ?_) (transferBound_constant_le _ _)
  intro m hm hml
  exact far_uniform_area M hM m hm (le_trans hml hl)

theorem qInverseDescending_close (M : Nat) (hM : 2≤M) (l : Nat) (hl : l≤M) :
    Close johnsonFiniteRelator (qInverseDescending l) (sigmaValue (sigmaDescendingWord 0 false l))
      (∑ i∈Finset.range l,(uniformFarCap M+1)*i^2) := by
  induction l with
  | zero => exact close_refl johnsonFiniteRelator 1
  | succ l ih =>
    have h := close_mul (close_inv (qSigma_uniform_close M hM l (by omega))) (ih (by omega))
    simpa only [qInverseDescending,sigmaDescendingWord,sigmaValue,List.map_cons,List.prod_cons,
      sigmaLetter,Bool.false_eq_true,↓reduceIte,zero_add,Finset.sum_range_succ,Nat.add_comm] using h

theorem sigmaDescendingWord_shift_value (m : ℤ) (b : Bool) (l : Nat) :
    johnsonP^m*sigmaValue (sigmaDescendingWord 0 b l)*(johnsonP^m)⁻¹=
      sigmaValue (sigmaDescendingWord m b l) := by
  induction l with
  | zero => simp [sigmaDescendingWord,sigmaValue]
  | succ l ih =>
    have hs : johnsonP^m*sigmaLetter ((l:ℤ),b)*(johnsonP^m)⁻¹=sigmaLetter (m+l,b) := by
      cases b
      · simp only [sigmaLetter,Bool.false_eq_true,↓reduceIte]
        rw [sigmaZ_shift m l]
        group
      · exact (sigmaZ_shift m l).symm
    simp only [sigmaDescendingWord,sigmaValue,List.map_cons,List.prod_cons,zero_add]
    change johnsonP^m*(sigmaLetter ((l:ℤ),b)*sigmaValue (sigmaDescendingWord 0 b l))*(johnsonP^m)⁻¹=
      sigmaLetter (m+l,b)*sigmaValue (sigmaDescendingWord m b l)
    rw [←hs,←ih]
    group

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.SigmaWord
#print axioms Blueprint.HoughtonProof.sigmaLetter
#print axioms Blueprint.HoughtonProof.sigmaValue
#print axioms Blueprint.HoughtonProof.sigmaDescendingWord
#print axioms Blueprint.HoughtonProof.sigmaInverseWord
#print axioms Blueprint.HoughtonProof.sigmaValue_append
#print axioms Blueprint.HoughtonProof.sigmaValue_inverse
#print axioms Blueprint.HoughtonProof.sigmaInverseWord_length
#print axioms Blueprint.HoughtonProof.sigmaInverseWord_indices
#print axioms Blueprint.HoughtonProof.sigmaDescendingWord_length
#print axioms Blueprint.HoughtonProof.sigmaDescendingWord_indices
#print axioms Blueprint.HoughtonProof.sigmaDescendingWord_value
#print axioms Blueprint.HoughtonProof.qInverseDescending
#print axioms Blueprint.HoughtonProof.qConjP_expansion
#print axioms Blueprint.HoughtonProof.transferBound_constant_le
#print axioms Blueprint.HoughtonProof.qSigma_uniform_close
#print axioms Blueprint.HoughtonProof.qInverseDescending_close
#print axioms Blueprint.HoughtonProof.sigmaDescendingWord_shift_value
