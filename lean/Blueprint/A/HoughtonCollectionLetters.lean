import Blueprint.A.HoughtonCollectionSteps

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev JohnsonWord := List (Fin 3 × Bool)

def johnsonLetter (a : Fin 3 × Bool) : FreeGroup (Fin 3) :=
  if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹

def deltaP (a : Fin 3 × Bool) : ℤ := if a.1=0 then if a.2 then 1 else -1 else 0
def deltaQ (a : Fin 3 × Bool) : ℤ := if a.1=1 then if a.2 then 1 else -1 else 0
def exponentP (w : JohnsonWord) : ℤ := (w.map deltaP).sum
def exponentQ (w : JohnsonWord) : ℤ := (w.map deltaQ).sum

def collectionLetterWord (m : ℤ) (l : Nat) (a : Fin 3 × Bool) : SigmaWord :=
  if a.1=0 then if a.2 then sigmaDescendingWord m false l
    else sigmaInverseWord (sigmaDescendingWord (m-1) false l)
  else if a.1=2 then [(m+l,a.2)] else []

theorem johnson_mk_cons (a : Fin 3 × Bool) (w : JohnsonWord) :
    FreeGroup.mk (a::w)=johnsonLetter a*FreeGroup.mk w := by
  change FreeGroup.mk ([a]++w)=_
  rw [←FreeGroup.mul_mk]
  rcases a with ⟨a,b⟩
  cases b <;> rfl

theorem delta_bounds (a : Fin 3 × Bool) :
    -1≤deltaP a ∧ deltaP a≤1 ∧ -1≤deltaQ a ∧ deltaQ a≤1 := by
  rcases a with ⟨a,b⟩
  fin_cases a <;> cases b <;> norm_num [deltaP,deltaQ]

theorem exponentP_cons (a : Fin 3 × Bool) (w : JohnsonWord) :
    exponentP (a::w)=deltaP a+exponentP w := rfl

theorem exponentQ_cons (a : Fin 3 × Bool) (w : JohnsonWord) :
    exponentQ (a::w)=deltaQ a+exponentQ w := rfl

theorem collectionLetter_length (m : ℤ) (l : Nat) (a : Fin 3 × Bool) (n : Nat)
    (hn : 1≤n) (hl : l≤2*n) : (collectionLetterWord m l a).length≤2*n := by
  unfold collectionLetterWord
  split
  · split <;> simpa only [sigmaInverseWord_length,sigmaDescendingWord_length] using hl
  · split <;> simp only [List.length_singleton,List.length_nil] <;> omega

theorem collectionLetter_indices (m : ℤ) (l : Nat) (a : Fin 3 × Bool) (n : Nat)
    (hm : 1≤m) (hmn : m≤2*n) (hl : l≤2*n) :
    ∀ x∈collectionLetterWord m l a, 0≤x.1 ∧ x.1≤4*n := by
  unfold collectionLetterWord
  split
  · split
    · intro x hx
      have h := sigmaDescendingWord_indices m false l x hx
      omega
    · apply sigmaInverseWord_indices
      intro x hx
      have h := sigmaDescendingWord_indices (m-1) false l x hx
      omega
  · split
    · intro x hx
      obtain rfl := List.mem_singleton.mp hx
      omega
    · simp

theorem collect_letter (n : Nat) (hn : 1≤n) (m : ℤ) (l : Nat) (hl : l≤2*n)
    (a : Fin 3 × Bool) :
    Close johnsonFiniteRelator (collectionState m l*johnsonLetter a)
      (sigmaValue (collectionLetterWord m l a)*collectionState (m+deltaP a) ((l:ℤ)+deltaQ a))
      (10*(uniformFarCap (4*n+2)+1)*n^3) := by
  have hM : 2≤4*n+2 := by omega
  have hlM : l≤4*n+2 := by omega
  rcases a with ⟨a,b⟩
  fin_cases a <;> cases b
  · simpa [johnsonP,johnsonQ,johnsonAlpha,johnsonLetter,collectionLetterWord,deltaP,deltaQ,sub_eq_add_neg] using
      close_weaken (collect_p_inverse (4*n+2) hM m l hlM) (collectionCost_le _ n l hn hl)
  · simpa [johnsonP,johnsonQ,johnsonAlpha,johnsonLetter,collectionLetterWord,deltaP,deltaQ] using
      close_weaken (collect_p (4*n+2) hM m l hlM) (collectionCost_le _ n l hn hl)
  · have he : collectionState m l*johnsonQ⁻¹=collectionState m ((l:ℤ)-1) := by
      dsimp [collectionState]
      rw [sub_eq_add_neg,zpow_add,zpow_neg_one]
      group
    have he' : collectionState m ((l:ℤ)+ -1)=collectionState m l*johnsonQ⁻¹ := by
      simpa only [sub_eq_add_neg] using he.symm
    simpa [johnsonP,johnsonQ,johnsonAlpha,johnsonLetter,collectionLetterWord,deltaP,deltaQ,sigmaValue,he'] using
      close_weaken (close_refl johnsonFiniteRelator (collectionState m l*johnsonQ⁻¹))
        (Nat.zero_le (10*(uniformFarCap (4*n+2)+1)*n^3))
  · have he : collectionState m l*johnsonQ=collectionState m ((l:ℤ)+1) := by
      dsimp [collectionState]
      rw [zpow_add,zpow_one]
      group
    simpa [johnsonP,johnsonQ,johnsonAlpha,johnsonLetter,collectionLetterWord,deltaP,deltaQ,sigmaValue,←he] using
      close_weaken (close_refl johnsonFiniteRelator (collectionState m l*johnsonQ))
        (Nat.zero_le (10*(uniformFarCap (4*n+2)+1)*n^3))
  · simpa [johnsonP,johnsonQ,johnsonAlpha,johnsonLetter,collectionLetterWord,deltaP,deltaQ,sigmaValue,sigmaLetter] using
      close_weaken (collect_alpha_inverse (4*n+2) hM m l hlM) (collectionAlphaCost_le _ n l hn hl)
  · simpa [johnsonP,johnsonQ,johnsonAlpha,johnsonLetter,collectionLetterWord,deltaP,deltaQ,sigmaValue,sigmaLetter] using
      close_weaken (collect_alpha (4*n+2) hM m l hlM) (collectionAlphaCost_le _ n l hn hl)

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.JohnsonWord
#print axioms Blueprint.HoughtonProof.johnsonLetter
#print axioms Blueprint.HoughtonProof.deltaP
#print axioms Blueprint.HoughtonProof.deltaQ
#print axioms Blueprint.HoughtonProof.exponentP
#print axioms Blueprint.HoughtonProof.exponentQ
#print axioms Blueprint.HoughtonProof.collectionLetterWord
#print axioms Blueprint.HoughtonProof.johnson_mk_cons
#print axioms Blueprint.HoughtonProof.delta_bounds
#print axioms Blueprint.HoughtonProof.exponentP_cons
#print axioms Blueprint.HoughtonProof.exponentQ_cons
#print axioms Blueprint.HoughtonProof.collectionLetter_length
#print axioms Blueprint.HoughtonProof.collectionLetter_indices
#print axioms Blueprint.HoughtonProof.collect_letter
