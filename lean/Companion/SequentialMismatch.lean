import Companion.SequentialDisturbance
import Companion.RecordProducts

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open TransferProof
set_option maxHeartbeats 600000

theorem projection_sign_mul {d : Nat} (Q : Mat d) (hQ : IsInvolution Q) (b : Bool) :
    boolPhase b • signProjection Q b=signProjection Q b*Q := by
  cases b <;> simp only [boolPhase,signProjection,Bool.false_eq_true,↓reduceIte,
    Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,Matrix.neg_mul,hQ.2]
  all_goals module

def sequentialMismatch {d n : Nat} (Q : Fin n → Mat d) (eta : Mat d) (j : Fin n) : ℝ :=
  familyHS (fun a => boolPhase (a j) • (CountProof.jointProjection n Q a*eta)-
    CountProof.jointProjection n Q a*eta*Q j)

theorem sequentialMismatch_last {d n : Nat} (Q : Fin (n+1) → Mat d)
    (hQ : ∀ j, IsInvolution (Q j)) (eta : Mat d) :
    sequentialMismatch Q eta (Fin.last n)=familyHS (fun a => Q (Fin.last n)*
      CountProof.jointProjection n (Fin.init Q) a*eta-
      CountProof.jointProjection n (Fin.init Q) a*eta*Q (Fin.last n)) := by
  unfold sequentialMismatch
  rw [familyHS_cube_snoc]
  simp_rw [jointProjection_snoc]
  simp only [Fin.snoc_last,Fin.init_snoc]
  have he : (fun t : Bool × (Fin n → Bool) =>
      boolPhase t.1 • ((signProjection (Q (Fin.last n)) t.1*CountProof.jointProjection n (Fin.init Q) t.2)*eta)-
      (signProjection (Q (Fin.last n)) t.1*CountProof.jointProjection n (Fin.init Q) t.2)*eta*Q (Fin.last n))=
      (fun t => signProjection (Q (Fin.last n)) t.1*(Q (Fin.last n)*
        CountProof.jointProjection n (Fin.init Q) t.2*eta-
        CountProof.jointProjection n (Fin.init Q) t.2*eta*Q (Fin.last n))) := by
    funext t
    rw [← Matrix.smul_mul,← Matrix.smul_mul,projection_sign_mul _ (hQ _) t.1]
    simp only [Matrix.mul_sub,Matrix.mul_assoc]
  rw [he]
  exact familyHS_pair_left (signProjection (Q (Fin.last n)))
    (CountProof.symmetryProjection_complete _ (hQ _))
    (fun a => Q (Fin.last n)*CountProof.jointProjection n (Fin.init Q) a*eta-
      CountProof.jointProjection n (Fin.init Q) a*eta*Q (Fin.last n))

theorem sequentialMismatch_castSucc {d n : Nat} (Q : Fin (n+1) → Mat d)
    (hQ : ∀ j, IsInvolution (Q j)) (eta : Mat d) (j : Fin n) :
    sequentialMismatch Q eta j.castSucc=sequentialMismatch (Fin.init Q) eta j := by
  unfold sequentialMismatch
  rw [familyHS_cube_snoc]
  simp_rw [jointProjection_snoc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,Fin.init_snoc]
  have he : (fun t : Bool × (Fin n → Bool) =>
      boolPhase (t.2 j) • ((signProjection (Q (Fin.last n)) t.1*CountProof.jointProjection n (Fin.init Q) t.2)*eta)-
      (signProjection (Q (Fin.last n)) t.1*CountProof.jointProjection n (Fin.init Q) t.2)*eta*Q j.castSucc)=
      (fun t => signProjection (Q (Fin.last n)) t.1*(boolPhase (t.2 j) •
        (CountProof.jointProjection n (Fin.init Q) t.2*eta)-
        CountProof.jointProjection n (Fin.init Q) t.2*eta*Q j.castSucc)) := by
    funext t
    simp only [Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_assoc]
  rw [he]
  exact familyHS_pair_left (signProjection (Q (Fin.last n)))
    (CountProof.symmetryProjection_complete _ (hQ _))
    (fun a => boolPhase (a j) • (CountProof.jointProjection n (Fin.init Q) a*eta)-
      CountProof.jointProjection n (Fin.init Q) a*eta*Q j.castSucc)

theorem familyHS_left_parseval {a : Type*} [Fintype a] {d : Nat} (K : a → Mat d)
    (hK : ∑ a, (K a).conjTranspose*K a=1) (A : Mat d) : familyHS (fun a => K a*A)=hsNorm A := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (hsNorm_nonneg _)).mp
  rw [familyHS_sq,CountProof.measurement_parseval K hK]

theorem mismatch_from_disturbance {a : Type*} [Fintype a] {d : Nat} (K : a → Mat d)
    (hK : ∑ a, (K a).conjTranspose*K a=1) (C eta : Mat d) :
    familyHS (fun a => C*K a*eta-K a*eta*C)≤hsNorm (comm C eta)+
      familyHS (fun a => comm C (K a)*eta) := by
  have he : (fun a => C*K a*eta-K a*eta*C)=
      (fun a => K a*comm C eta+comm C (K a)*eta) := by
    funext a
    simp only [comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := familyHS_add (fun a => K a*comm C eta) (fun a => comm C (K a)*eta)
  rw [familyHS_left_parseval K hK (comm C eta)] at h
  exact h

theorem sequential_mismatch_uniform {d : Nat} (n : Nat) (Q : Fin n → Mat d)
    (hQ : ∀ j, IsInvolution (Q j)) (eta : Mat d) (c k : ℝ)
    (hc : ∀ j, hsNorm (comm (Q j) eta)≤c)
    (hk : ∀ j l, hsNorm (comm (Q j) (Q l)*eta)≤k) (j : Fin n) :
    sequentialMismatch Q eta j≤c+(j.val:ℝ)*k/Real.sqrt 2+
      (j.val:ℝ)*((j.val:ℝ)-1)*c/2 := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [sequentialMismatch_last Q hQ eta]
      have h := mismatch_from_disturbance (CountProof.jointProjection n (Fin.init Q))
        (CountProof.jointProjection_complete _ _ (fun j => hQ j.castSucc)) (Q (Fin.last n)) eta
      have hb := sequential_disturbance_uniform n (Fin.init Q) (fun j => hQ j.castSucc)
        (Q (Fin.last n)) eta (hQ _) c k (fun j => hc j.castSucc) (fun j => hk _ j.castSucc)
      simp only [Fin.val_last]
      linarith [hc (Fin.last n)]
    · rw [sequentialMismatch_castSucc Q hQ eta j]
      exact ih (Fin.init Q) (fun j => hQ j.castSucc) (fun j => hc j.castSucc)
        (fun j l => hk j.castSucc l.castSucc) j

end
end Companion.Analytic.ReturnProof
