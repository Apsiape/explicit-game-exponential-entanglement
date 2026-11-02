import Companion.TransferWords

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

/-- An exact Alice parity equation gives the ordered Bob relation with
the row-length constant, on the original coefficient matrix. -/
theorem linear_relation_bound {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (L : List (Mat dB × Mat dA)) (theta : ℝ)
    (hL : ∀ p ∈ L, IsUnitary p.1 ∧ IsUnitary p.2)
    (he : ∀ p ∈ L, hsNorm (p.1*psi-psi*p.2)≤theta)
    (c : ℂ) (hc : c*c=1) (hcn : ‖c‖=1)
    (hparity : (L.map Prod.snd).prod=c • (1:Mat dA)) :
    hsNorm ((c • (L.map Prod.fst).prod-1)*psi)≤(L.length:ℝ)*theta := by
  have h := intertwining_word_uniform psi L theta hL he
  have hm : (c • (L.map Prod.fst).prod-1)*psi=
      c • ((L.map Prod.fst).prod*psi-psi*(L.map Prod.snd).prod) := by
    rw [hparity,smul_sub,Matrix.mul_smul,Matrix.mul_one,smul_smul,hc,one_smul,
      Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul]
  rw [hm,CountProof.factor_hs_smul,hcn,one_mul]
  exact h

theorem theta_nonneg (g : LCS) (eps : ℝ) : 0≤theta g eps := by
  unfold theta
  positivity

theorem transferPrecision_nonneg (g : LCS) (eps : ℝ) : 0≤transferPrecision g eps := by
  exact mul_nonneg (le_trans (by norm_num : (0:ℝ)≤4) (le_max_right _ _)) (theta_nonneg g eps)

theorem linear_transfer_constant (g : LCS) (eps : ℝ) (q : Nat) (hq : q≤g.arity) :
    (q:ℝ)*theta g eps≤transferPrecision g eps := by
  apply mul_le_mul_of_nonneg_right _ (theta_nonneg g eps)
  exact (by exact_mod_cast hq : (q:ℝ)≤g.arity).trans (le_max_left _ _)

theorem commutator_transfer_constant (g : LCS) (eps : ℝ) :
    4*theta g eps≤transferPrecision g eps :=
  mul_le_mul_of_nonneg_right (le_max_right _ _) (theta_nonneg g eps)

end
end Companion.Analytic.TransferProof
