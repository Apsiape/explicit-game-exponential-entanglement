import Challenge
import Blueprint.A.Diagram.Proof

open Companion Companion.Analytic Blueprint Blueprint.Published

-- These annotations check the proved roots, without using admitted proofs.
example : Blueprint.Published.TensorPerfectFinite → Blueprint.AStatement := @Blueprint.theoremA
example : Blueprint.Published.ConjugatorLengths := @Blueprint.DiagramProof.conjugatorLengths
example : Blueprint.Published.TensorPerfectFinite → Blueprint.AStatement := @Blueprint.DiagramProof.theoremA
example : Blueprint.Published.PauliHashModels := @Blueprint.Published.pauliHashModels
example : Companion.Analytic.Count := @Companion.Analytic.CountProof.count
example : Companion.Analytic.UniformCount := @Companion.Analytic.CountProof.uniformCount
example : Companion.Analytic.Transfer := @Companion.Analytic.TransferProof.transfer
example : Companion.Analytic.Return := @Companion.Analytic.ReturnProof.returnTheorem
example : Companion.Analytic.ReturnExistence := @Companion.Analytic.ReturnProof.returnExistence
example : Companion.Analytic.TwoSided := @Companion.Analytic.ProfileProof.twoSided
example : Blueprint.EStatement := @Blueprint.theoremE
example : Blueprint.FStatement := @Blueprint.theoremF

-- The six frozen challenge declarations are consulted only as type data.
-- No expression referring to an admitted challenge proof is constructed.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pairs := #[
    (`Companion.Analytic.CountProof.count, `Challenge.count),
    (`Companion.Analytic.CountProof.uniformCount, `Challenge.uniformCount),
    (`Companion.Analytic.TransferProof.transfer, `Challenge.transfer),
    (`Companion.Analytic.ReturnProof.returnTheorem, `Challenge.returnTheorem),
    (`Companion.Analytic.ReturnProof.returnExistence, `Challenge.returnExistence),
    (`Companion.Analytic.ProfileProof.twoSided, `Challenge.twoSided)]
  for (proved, frozen) in pairs do
    let some p := env.find? proved | throwError "Missing proved declaration {proved}"
    let some f := env.find? frozen | throwError "Missing frozen declaration {frozen}"
    unless p.type == f.type do
      throwError "Frozen type mismatch: {proved} versus {frozen}"
    logInfo m!"Frozen type agrees: {proved}"

#check @Blueprint.theoremA
#print axioms Blueprint.theoremA
#check @Blueprint.DiagramProof.conjugatorLengths
#print axioms Blueprint.DiagramProof.conjugatorLengths
#check @Blueprint.DiagramProof.theoremA
#print axioms Blueprint.DiagramProof.theoremA
#check @Blueprint.Published.pauliHashModels
#print axioms Blueprint.Published.pauliHashModels
#check @Companion.Analytic.CountProof.count
#print axioms Companion.Analytic.CountProof.count
#check @Companion.Analytic.CountProof.uniformCount
#print axioms Companion.Analytic.CountProof.uniformCount
#check @Companion.Analytic.TransferProof.transfer
#print axioms Companion.Analytic.TransferProof.transfer
#check @Companion.Analytic.ReturnProof.returnTheorem
#print axioms Companion.Analytic.ReturnProof.returnTheorem
#check @Companion.Analytic.ReturnProof.returnExistence
#print axioms Companion.Analytic.ReturnProof.returnExistence
#check @Companion.Analytic.ProfileProof.twoSided
#print axioms Companion.Analytic.ProfileProof.twoSided
#check @Blueprint.theoremE
#print axioms Blueprint.theoremE
#check @Blueprint.theoremF
#print axioms Blueprint.theoremF
#check @Blueprint.DiagramProof.merge_matching
#print axioms Blueprint.DiagramProof.merge_matching
#check @Blueprint.ASector.source_sector
#print axioms Blueprint.ASector.source_sector
#check @Blueprint.AHash.general_hash_models
#print axioms Blueprint.AHash.general_hash_models

namespace Blueprint.DiagramProof
open Companion Companion.Analytic Blueprint Blueprint.Published
open Blueprint.ConjugatorCollapse OAI.TorsionFreeZeroDivisors
example (a z p q : Word) (e : Nat × Bool) (pre post : List Word)
    (d : WordBlocks.Matching inverse
      ((a ++ [e] ++ z) :: (pre ++ (p ++ [inverse e] ++ q) :: post)))
    (hp : d.partner (Sum.inl (edgeAt a e z)) =
      Sum.inr (blockAt pre (p ++ [inverse e] ++ q) post (edgeAt p (inverse e) q))) :
    Nonempty (WordBlocks.Matching inverse ((a ++ q ++ p ++ z) :: (pre ++ post))) := merge_matching a z p q e pre post d hp
end Blueprint.DiagramProof

namespace Blueprint.ASector
open Companion Companion.Analytic Blueprint Blueprint.Published
example
    (hconj : Published.ConjugatorLengths)
    {d : Nat} (U : Nat → Mat d) (s : State d) (e delta : ℝ)
    (he : 0<e) (hd : 0<delta) (hd2 : delta≤2) (hm : sourceModel U s e)
    (hv : delta≤hs ((wordEval U lampJ-1)*s.xi)) (hsmall : e≤(2:ℝ)^(-1071:ℤ)*delta) :
    sourceC/16*delta^4/e^2*bfun e-1≤entropy s.rho ∧
      sourceC*delta^2/e^2*bfun e≤log2 (rank s.rho:ℝ) := source_sector hconj U s e delta he hd hd2 hm hv hsmall
end Blueprint.ASector

namespace Blueprint.AHash
open Companion Companion.Analytic Blueprint Blueprint.Published
example (hhash : Published.PauliHashModels)
    (R : List Word) (ell : Nat) (hell : 1≤ell)
    (hL : ∀ r∈R, r.length≤ell) (hR : ∀ r∈R, Concrete.gpPlusWordHom (FreeGroup.mk r)=1)
    (e : ℝ) (he : 0<e) (he1 : e≤1) :
    ∃ d : Nat, 0<d ∧ ∃ U : Nat → Mat d, normalizedRepresentation R U e ∧
      U 5*U 5=1 ∧ U 6*U 6=1 ∧ wordEval U lampJ=-1 ∧
      log2 d≤336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8 ∧
      log2 d≤400*(ell:ℝ)^2/e^2*log2 (2*ell/e) := general_hash_models hhash R ell hell hL hR e he he1
end Blueprint.AHash
