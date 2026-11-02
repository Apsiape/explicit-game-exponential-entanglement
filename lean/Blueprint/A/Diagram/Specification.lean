import Blueprint.A.Diagram.Blocks
import Blueprint.A.ConjugatorCollapse

/-! Finite word-boundary diagrams. Planarity is the literal componentwise Euler
identity of a rotation permutation and a fixed-point-free inverse-letter matching.
Faces retain original relators and orientation bits. No shellability field occurs. -/
namespace Blueprint.DiagramProof
open Companion Published ConjugatorCollapse
open OAI.TorsionFreeZeroDivisors
set_option maxHeartbeats 800000
abbrev Face := Word × Bool
def inverse (e : Nat × Bool) : Nat × Bool := (e.1,!e.2)
def faceWord (f : Face) : Word := signedWord f.1 f.2
def blockAt (pre : List Word) (w : Word) (post : List Word)
    (i : Fin w.length) : WordBlocks.Occ (pre ++ w :: post) :=
  match pre with
  | [] => Sum.inl i
  | _v :: pre => Sum.inr (blockAt pre w post i)
def edgeAt (a : Word) (e : Nat × Bool) (z : Word) : Fin (a ++ [e] ++ z).length :=
  ⟨a.length,by simp only [List.length_append,List.length_singleton]; omega⟩
structure Diagram (R : Finset Word) (K : Nat) (u : Word) (n : Nat) where
  faces : List Face
  count : faces.length = n
  valid : ∀ f ∈ faces, f.1 ∈ R ∧ f.1.length ≤ K
  matching : WordBlocks.Matching inverse (u :: faces.map faceWord)
/-- An actual matched exterior/interior pair, with the chosen original face
and every untouched face retained. The two selected letters are explicit. -/
structure Contact (R : Finset Word) (K : Nat) (u : Word) (n : Nat) where
  pre : List Face
  post : List Face
  original : Word
  positive : Bool
  before : Word
  after : Word
  left : Word
  right : Word
  edge : Nat × Bool
  source : u = before ++ [edge] ++ after
  original_mem : original ∈ R
  original_length : original.length ≤ K
  original_split : signedWord original positive = left ++ [inverse edge] ++ right
  count : pre.length + post.length + 1 = n
  valid : ∀ f ∈ pre ++ post, f.1 ∈ R ∧ f.1.length ≤ K
  matching : WordBlocks.Matching inverse
    ((before ++ [edge] ++ after) ::
      (pre.map faceWord ++ (left ++ [inverse edge] ++ right) :: post.map faceWord))
  paired : matching.partner (Sum.inl (edgeAt before edge after)) =
    Sum.inr (blockAt (pre.map faceWord) (left ++ [inverse edge] ++ right)
      (post.map faceWord) (edgeAt left (inverse edge) right))
end Blueprint.DiagramProof
