import Lake
open Lake DSL
-- QuAIR upstream commit 8a931d4bda61ba503cfc0728704cfef5dedf2cff.
-- The only QIT source change is the documented ContinuousENorm API rename.
package LeanQIT where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from "../mathlib"
lean_lib QIT

