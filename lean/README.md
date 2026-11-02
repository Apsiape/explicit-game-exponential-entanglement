# Lean proof accompanying version 1.1.0

This directory packages the certified source roots without changing any proof
or statement bytes. The original certification reports the listed roots free
of `sorryAx`, with only `[propext, Classical.choice, Quot.sound]`, and successful
selected-root replays by Lean's `leanchecker` and the independent `nanoda`
checker. This release tree was then rebuilt from scratch and replayed
independently (1 November 2026): the release configuration compiled all 309
retained modules and the final Audit with Lean 4.35.0, all 15 selected roots
printed exactly `[propext, Classical.choice, Quot.sound]`, and the selected-root
export was accepted by both `leanchecker` and `nanoda`.

## Proved roots

- `Blueprint.theoremA : Blueprint.Published.TensorPerfectFinite → Blueprint.AStatement`

  Theorem A, including exclusion of perfect spatial strategies, conditional only on the published tensor-strategy clause.

- `Blueprint.DiagramProof.conjugatorLengths : Blueprint.Published.ConjugatorLengths`

  Lemma 3.4: original relators and signs, at most k conjugates, every conjugator at most |w| + kK.

- `Blueprint.DiagramProof.theoremA : Blueprint.Published.TensorPerfectFinite → Blueprint.AStatement`

  A second wrapper of Theorem A with exactly the same parameter.

- `Blueprint.Published.pauliHashModels : Blueprint.Published.PauliHashModels`

  Finite Pauli hash models used in the upper bound.

- `Companion.Analytic.CountProof.count : Companion.Analytic.Count`

  All three parts of the finite-dimensional qubit count, Theorem 4.1.

- `Companion.Analytic.CountProof.uniformCount : Companion.Analytic.UniformCount`

  The uniform-error entropy and rank bounds, Corollary 4.2 and Theorem C.

- `Companion.Analytic.TransferProof.transfer : Companion.Analytic.Transfer`

  Finite-dimensional Theorem 5.1: Schmidt-support compression, full-rank state, exact J = -I and preservation of Bob's reduced state.

- `Companion.Analytic.ReturnProof.returnTheorem : Companion.Analytic.Return`

  Finite-dimensional Theorem 5.4 with the specified rounded observables and sequential measurement, including zero error.

- `Companion.Analytic.ReturnProof.returnExistence : Companion.Analytic.ReturnExistence`

  The positive-error existence consequence of Theorem 5.4.

- `Companion.Analytic.ProfileProof.twoSided : Companion.Analytic.TwoSided`

  All three finite-dimensional profile comparisons of Corollary 5.5: dimension, entropy and fixed-dimension precision/loss.

- `Blueprint.theoremE : Blueprint.EStatement`

  CHSH(n) pure entropy bounds, profiles, mixed entanglement-of-formation lower bound and both asymptotic rates.

- `Blueprint.theoremF : Blueprint.FStatement`

  K profiles, the Slofstra-Vidick game dimension rate, value one and the logarithmic rate.

The three additional certified adapters printed by the final audit are:
`Blueprint.DiagramProof.merge_matching`, `Blueprint.ASector.source_sector`,
and `Blueprint.AHash.general_hash_models`. Their exact signatures are in the
final examples of Audit.lean. The first proves the literal cyclic-boundary
merge used in the conjugator proof. The sector adapter assumes
`Published.ConjugatorLengths` and proves the stated entropy and rank bounds;
the hash-model adapter assumes `Published.PauliHashModels` and supplies finite
representations with the explicit dimension bounds and exact marked sign.
Both parameters are supplied by proved terms in the production Theorem A
assembly. Neither is an extra parameter of `Blueprint.theoremA`.

The following exact signatures use the same open namespaces as Audit.lean.

```lean
Blueprint.DiagramProof.merge_matching (a z p q : Word) (e : Nat × Bool) (pre post : List Word)
    (d : WordBlocks.Matching inverse
      ((a ++ [e] ++ z) :: (pre ++ (p ++ [inverse e] ++ q) :: post)))
    (hp : d.partner (Sum.inl (edgeAt a e z)) =
      Sum.inr (blockAt pre (p ++ [inverse e] ++ q) post (edgeAt p (inverse e) q))) :
    Nonempty (WordBlocks.Matching inverse ((a ++ q ++ p ++ z) :: (pre ++ post)))
```

```lean
Blueprint.ASector.source_sector
    (hconj : Published.ConjugatorLengths)
    {d : Nat} (U : Nat → Mat d) (s : State d) (e delta : ℝ)
    (he : 0<e) (hd : 0<delta) (hd2 : delta≤2) (hm : sourceModel U s e)
    (hv : delta≤hs ((wordEval U lampJ-1)*s.xi)) (hsmall : e≤(2:ℝ)^(-1071:ℤ)*delta) :
    sourceC/16*delta^4/e^2*bfun e-1≤entropy s.rho ∧
      sourceC*delta^2/e^2*bfun e≤log2 (rank s.rho:ℝ)
```

```lean
Blueprint.AHash.general_hash_models (hhash : Published.PauliHashModels)
    (R : List Word) (ell : Nat) (hell : 1≤ell)
    (hL : ∀ r∈R, r.length≤ell) (hR : ∀ r∈R, Concrete.gpPlusWordHom (FreeGroup.mk r)=1)
    (e : ℝ) (he : 0<e) (he1 : e≤1) :
    ∃ d : Nat, 0<d ∧ ∃ U : Nat → Mat d, normalizedRepresentation R U e ∧
      U 5*U 5=1 ∧ U 6*U 6=1 ∧ wordEval U lampJ=-1 ∧
      log2 d≤336*ell/e^2*log2 (2*ell/e)+8*(ell:ℝ)^2/e^2+4*log2 (2*ell/e)+8 ∧
      log2 d≤400*(ell:ℝ)^2/e^2*log2 (2*ell/e)
```


The A aggregate in Blueprint.lean states 1993 variables, 1687 equations, arity
three, value one, no finite perfect strategy, no perfect spatial strategy,
`MainPureLower`, `MainMixedLower`, `MainUpper` and the two dimension-profile
exponents. Constants are `mainC = 49/10^35`, `mainEps = 2^(-5500)`, and
`mainUpperC = 74000000000`; `bfun` is the paper's beta factor. The pure lower
bound includes entropy at most log rank, the mixed bound is the countable
convex-roof entanglement of formation, and the upper bound uses the maximally
entangled profile. The entropy asymptotic follows from the lower/upper bounds;
it is not a separate entropy-limit conjunct. A additionally excludes perfect
spatial strategies, beyond the introduction's finite-dimensional exclusion.

EStatement is `ELower ∧ EProfiles ∧ EMixed ∧` the pure and formation
`ThetaRate` conclusions. The pure numeric lower coefficient is 1/60000000.
The mixed lower bound uses `chshM n (2*eps)/4`, where
`chshM n eps = floor(min(n, 10^(-7)/eps)/3)`; this implies the paper's
1/240000000 coefficient and -1/4 offset. The upper profiles are obtained from
pure-state constructions, with `min(floor(n/2), ceil(1/eps))` ebits.
FStatement is `KProfile ∧ FSVGame.GameRate ∧ quantumValueOne FSVGame.game ∧
FSVGame.LogRate`: the K bounds have `0 < delta ≤ 2`, and the game bounds have
`0 < eps ≤ 1`. See RatesDefinitions.lean and FSVGame.lean for exact quantifiers.

## Published parameter and scope

`Blueprint.Published.TensorPerfectFinite` is a theorem parameter, not a
registered Lean axiom. It says that a perfect projective tensor strategy for
the development's linear-system instances has a finite-dimensional operator
solution (Hermitian involutions, same-row commutativity and signed row products).
The source is [Cleve, Liu and Slofstra, arXiv:1606.02278v1](https://arxiv.org/pdf/1606.02278v1),
Definition 1 and Theorem 5, (1) implies (2), including the paragraph removing
separability. Their Theorem 5 attributes this implication to Cleve and Mittal.
It contains no short-conjugator claim or quantitative bound from this paper.
The spatial POVM dilations, answer coarsening, pointwise perfect-score argument
and finite-strategy adaptations are separately proved in the retained sources.

The analytic statements use finite matrices; rows of an LCS are nonempty,
sorted, duplicate-free and bounded, with an admissible distribution. Operators
on the free group are encoded by generator assignments and word evaluation.
The LCS dimension, entropy and precision-loss profiles and the K profiles use extended nonnegative infima, where an empty
feasible set gives infinity; the CHSH entropy and formation profiles (`Blueprint.chshEntropyProfile`,
`Blueprint.EAsymptotics.formationProfile`) are real-valued infima, with feasible constructions on the stated E domains.
The sector root exposes entropy/rank inequalities rather than every intermediate
sector-state fact as a conjunct. There is no standalone certified Theorem B,
no proof of the external tensor-strategy implication, and no claim of a
formalization of every manuscript proposition, literature citation, appendix,
numerical experiment or prose statement.

Challenge.lean is frozen, including its eleven historical admitted declarations
and older comments. The final Audit.lean checks the six analytic roots against
the types of those frozen declarations by inspecting type data only; it never
uses their admitted proof terms. A/E/F and the extra combinatorial/adapter types
are checked against their transparent propositions/signatures, which were
introduced beyond that frozen file. No proof module imports Challenge.lean.
After checking the published parameter, the remaining point of trust is that the definitions in Challenge.lean mean what the paper means.

## Toolchain, dependencies and source identity

Lean: 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Mathlib: v4.35.0, commit 56a005855ea17e0b0958f73ec801ae140b0a1679.
All ten path dependencies are retained under vendor/ to preserve resolution
without changing proof imports or the package manifest. Full dependency source
packages are included, excluding generated build files and caches; only the
imported part is a proof dependency. Their upstream revisions and archive
hashes are in DEPENDENCIES.json; licence notices remain in every package.

| Package | Licence | Files | Bytes |
|---|---|---:|---:|
| aesop | [Apache-2.0](vendor/aesop/LICENSE) | 258 | 833512 |
| batteries | [Apache-2.0](vendor/batteries/LICENSE) | 300 | 1480231 |
| Cli | [MIT](vendor/Cli/LICENSE) | 12 | 115346 |
| importGraph | [Apache-2.0](vendor/importGraph/LICENSE) | 105 | 662909 |
| LeanQIT | [Apache-2.0](vendor/LeanQIT/LICENSE) | 420 | 13243049 |
| LeanSearchClient | [Apache-2.0](vendor/LeanSearchClient/LICENSE) | 15 | 54854 |
| mathlib | [Apache-2.0](vendor/mathlib/LICENSE) | 9391 | 103817535 |
| plausible | [Apache-2.0](vendor/plausible/LICENSE) | 35 | 163599 |
| proofwidgets | [Apache-2.0](vendor/proofwidgets/LICENSE) | 109 | 9591412 |
| Qq | [Apache-2.0](vendor/Qq/LICENSE) | 35 | 111634 |

The 309 project modules are listed in SOURCE-MANIFEST.json; their source bytes
match the certification receipts. Challenge.lean and all mathematical sources
are unchanged. The release-only configuration and sanitized diagram provenance
are the declared exceptions; no import was edited.

- lakefile.lean original SHA-256: `5612f95c841ed37ad4cffb1d23b5f719d8df639b78347f0ca6853af9ff795516`
- lakefile.lean release SHA-256: `6852445a5a2fe3224c509a07f1f71a94b063e1f99a207970d3f9ce0fc653fb55`
- lake-manifest.json original SHA-256: `9ed3f1d6a56fb17fb34e8cd2779b11e7fb38532162d8aa5d759f1dedbc824d36`
- lake-manifest.json release SHA-256: `9ed3f1d6a56fb17fb34e8cd2779b11e7fb38532162d8aa5d759f1dedbc824d36`
- diagram provenance original SHA-256: `6a0bef620edefe0e30376d4d9629399b0a2514f0e0120125abfaeb3bc8eb4178`
- diagram provenance release SHA-256: `8b6fe43b87928993313a4176ca96032db788064b232ea6052975c3548fc6736b`

The manifest is byte-identical. The release lakefile enumerates exactly the
309 retained modules and final Audit; it contains no historical audit target.
The diagram provenance removes only its local source locator; upstream origins,
commits and source hashes are preserved. SOURCE-MANIFEST.json records every
copied Lean/dependency file's SHA-256 and byte comparison. See
THIRD-PARTY-NOTICES.md for locally ported proofs and retained licences.

## Build and replay

From `lean/`, with the pinned Lean toolchain selected, run one Lean build at a time:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

On Windows, `lake build` can run Windows PowerShell, Node.js and npm through ProofWidgets (a Mathlib dependency) to
refresh its widget package lock, even though the widget JavaScript is shipped: keep `powershell` and Node.js on PATH.
That step treats the shipped lock as an output, so it can re-resolve JavaScript package versions and rewrite the lock
and the widget bundles. The widgets play no part in any proof, and no Lean source changes.

The selected declaration export uses the Lean 4.35.0 `lean4export` tool
(executable name `leanexport`) and its matching `leanchecker`; install these
checker executables on PATH separately if the selected distribution does not
include them. Use a shell whose native redirection preserves UTF-8 bytes
(e.g. POSIX sh or Windows cmd):

```sh
lake env leanexport Audit -- Blueprint.theoremA Blueprint.DiagramProof.conjugatorLengths Blueprint.DiagramProof.theoremA Blueprint.Published.pauliHashModels Companion.Analytic.CountProof.count Companion.Analytic.CountProof.uniformCount Companion.Analytic.TransferProof.transfer Companion.Analytic.ReturnProof.returnTheorem Companion.Analytic.ReturnProof.returnExistence Companion.Analytic.ProfileProof.twoSided Blueprint.theoremE Blueprint.theoremF Blueprint.DiagramProof.merge_matching Blueprint.ASector.source_sector Blueprint.AHash.general_hash_models Quot Quot.mk Quot.lift Quot.ind propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam > proofs.ndjson
lake env leanchecker --silent --from-export proofs.ndjson
nanoda nanoda.json
```

Create `nanoda.json` in the working directory with:

```json
{
  "use_stdin": false,
  "export_file_path": "proofs.ndjson",
  "permitted_axioms": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ],
  "unpermitted_axiom_hard_error": true,
  "num_threads": 1,
  "nat_extension": true,
  "string_extension": true
}
```

The independent nanoda executable must support the Lean 4.35.0 export schema.
The Windows replays used a 128 MiB PE stack reservation for nanoda; an equivalent
resource limit may be needed for that platform. The independent replay of this
release tree ran one Lean process at a time (`-j1`, one thread) with an 8 GiB
heap limit per Lean process (`-M8192`) and a 14 GiB limit on the whole process
tree; with 4 GiB for the whole tree, imports of Mathlib-scale objects failed.
The build took about 91 minutes, and both checkers exited successfully.

## Expected build output

`lake build` compiles the retained dependency closure and the single final
Audit. The unchanged Challenge.lean may emit warnings for its eleven historical
`sorry` declarations; this is not a claim that the proved roots use them.
The final audit emits six `Frozen type agrees:` messages, exact-type `#check`
lines, and `#print axioms` lines for all 15 selected roots. The expected root
axioms are `[propext, Classical.choice, Quot.sound]`, never `sorryAx`.
Unchanged source modules also print some intermediate axiom information.
Dependency build progress and warning text can vary with the compiler/cache;
any root `sorryAx`, frozen type mismatch or compilation failure is a failed
release replay and must be investigated.

## Licence

The authors' Lean development is Apache-2.0 unless a source says otherwise;
see [the licence](../LICENSES/Apache-2.0.txt), [RIGHTS.md](../RIGHTS.md) and
[third-party notices](THIRD-PARTY-NOTICES.md). Vendored source headers and
licences retain their own terms.
