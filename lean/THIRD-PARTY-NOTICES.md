# Third-party proof ports

The vendored packages retain their original licences and notices. Origins,
commits and archive hashes are recorded in DEPENDENCIES.json. Each package is
copied from the certified dependency tree without source edits; generated build
files and caches are excluded. LeanQIT retains its documented Lean 4.35
compatibility adaptation and its original PORT-PROVENANCE.json.

The Apache-2.0 diagram proof ports from OpenAI/math retain their source headers,
upstream commit, source hashes, selected ranges and modification descriptions in
Blueprint/A/Diagram/PROVENANCE.json, together with LICENSE-APACHE-2.0-OpenAI.
The release provenance omits the original local source locator.

Two local Apache-2.0 proof ports from QuAIR/Lean-QIT commit
8a931d4bda61ba503cfc0728704cfef5dedf2cff are retained with attribution:

| Local declaration | Upstream source |
|---|---|
| Companion.Analytic.quair_entropy_isometry and root-multiset helpers | QIT/Information/Renyi/AlphaEntropyContinuity.lean |
| Companion.Analytic.CountProof.pure_entropy_zero | QIT/Information/AlickiFannesWinter.lean |

The square-root/trace-cyclicity argument in TransferProof.psd_trace_mul_nonneg
is also credited to QIT/Util/SDP/HermitianPSDTraceDuality.lean; that module is not
imported. See vendor/LeanQIT/LICENSE for the upstream Apache-2.0 licence.
