import Blueprint.A.HoughtonInputs
import Blueprint.A.PairWords

namespace Blueprint.Published
noncomputable section
open Companion ASector PairProof

abbrev Letter := Fin 6

def decode (j : Nat) : Letter := ⟨(j-1)%6,Nat.mod_lt _ (by decide)⟩
def encode (j : Letter) : Nat := j.val+1
def paperRelator (i : Fin 27) : FreeGroup Letter := FreeGroup.map decode (pauliRelator i)

/-- The word omega of Lemma 7.3(a), with points numbered from zero.
The two arguments may be reversed; equal arguments give the empty word. -/
def omegaWord (i j : Nat) : Word :=
  let l := min i j
  let h := max i j
  let s : Word := [(1,true),(2,true),(1,false),(2,false)]
  if i=j then [] else
    List.replicate l (1,true) ++
    (List.replicate (h-l-1) (s++[(1,true)])).flatten ++
    (List.replicate (h-l-1) (s++[(1,false)])).flatten ++
    s ++ List.replicate l (1,false)

def singleWord (i : Nat) : Word := omegaWord 0 i
def doubleWord (i j : Nat) : Word :=
  omegaWord 0 j ++ omegaWord 1 (Equiv.swap 0 j i)
def tauWord (i : Nat) : Word := transportLamp (singleWord i) 3
def transvectionWord (i j : Nat) : Word := transportLamp (doubleWord i j) 4
def paperTau (i : Nat) : FreeGroup Letter := FreeGroup.map decode (FreeGroup.mk (tauWord i))
def paperX (i j : Nat) : FreeGroup Letter := FreeGroup.map decode (FreeGroup.mk (transvectionWord i j))
def paperLamp (a : Fin 2) : FreeGroup Letter := FreeGroup.of ⟨a.val+4,by omega⟩
def localC (n : Nat) : Nat := 2*dehnH (1500*n)+130*n
def localL (n : Nat) : Nat := 10*dehnH (1500*n)+700*n

/-- Exact named literature input: Mghirbi--Douglas v1.0.0, Lemma 7.7
(Local fillings), parts (a)--(d). The words are Definition 7.5, built using
the omega words and the permutation recursion of Lemma 7.3. The free group
has precisely the paper's six generators. Area means a product of conjugates
of the 27 relators of Definition 7.1. No proof is asserted here. -/
def LocalFillings : Prop := ∀ n : Nat, 3≤n →
  (∀ i : Fin n, FiniteArea.Area paperRelator (paperTau i.val*paperTau i.val) 1) ∧
  (∀ i j : Fin n, i≠j →
    FiniteArea.Area paperRelator (groupComm (paperTau i.val) (paperTau j.val)) (4*localC n+1)) ∧
  (∀ i j : Fin n, i≠j → ∀ k : Fin n,
    FiniteArea.Area paperRelator
      (paperX i.val j.val*paperTau k.val*(paperX i.val j.val)⁻¹*
        (if k=j then paperTau j.val*paperTau i.val else paperTau k.val)⁻¹) (5*localC n+1)) ∧
  (∀ i j : Fin n, i≠j → ∀ a : Fin 2,
    FiniteArea.Area paperRelator (groupComm (paperX i.val j.val) (paperLamp a))
      (2*(doubleWord i.val j.val).length+1)) ∧
  (∀ i : Fin n, ∀ a b : Fin 2,
    FiniteArea.Area paperRelator
      (groupComm (paperLamp a) (paperTau i.val*paperLamp b*(paperTau i.val)⁻¹))
      (4*(singleWord i.val).length+1))

end
end Blueprint.Published

#print axioms Blueprint.Published.Letter
#print axioms Blueprint.Published.decode
#print axioms Blueprint.Published.encode
#print axioms Blueprint.Published.paperRelator
#print axioms Blueprint.Published.omegaWord
#print axioms Blueprint.Published.singleWord
#print axioms Blueprint.Published.doubleWord
#print axioms Blueprint.Published.tauWord
#print axioms Blueprint.Published.transvectionWord
#print axioms Blueprint.Published.paperTau
#print axioms Blueprint.Published.paperX
#print axioms Blueprint.Published.paperLamp
#print axioms Blueprint.Published.localC
#print axioms Blueprint.Published.localL
#print axioms Blueprint.Published.LocalFillings
