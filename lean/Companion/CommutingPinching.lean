import Companion.PinchingEntropy

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

variable {a : Type*} [Fintype a] [DecidableEq a]

def channelRun : (n : Nat) → (Fin n → QIT.Channel a a) → QIT.Channel a a
  | 0,_ => QIT.Channel.idChannel a
  | n+1,T => (channelRun n (Fin.tail T)).comp (T 0)

/-- Data processing bounds the accumulated entropy gain of commuting
entropy-projection channels by the sum of their gains on the initial state. -/
theorem channelRun_entropy (n : Nat) (T : Fin n → QIT.Channel a a)
    (hgain : ∀ i (rho : QIT.State a), rho.relativeEntropy ((T i).applyState rho)=
      ((((T i).applyState rho).vonNeumann-rho.vonNeumann:ℝ):EReal))
    (hcomm : ∀ i j (rho : QIT.State a), (T i).applyState ((T j).applyState rho)=
      (T j).applyState ((T i).applyState rho)) (rho : QIT.State a) :
    ((channelRun n T).applyState rho).vonNeumann-rho.vonNeumann≤
      ∑ i, (((T i).applyState rho).vonNeumann-rho.vonNeumann) := by
  induction n generalizing rho with
  | zero => simp [channelRun,QIT.State.idChannel_applyState]
  | succ n ih =>
    have ht := ih (fun j => T j.succ) (fun j sigma => hgain j.succ sigma)
      (fun i j sigma => hcomm i.succ j.succ sigma) ((T 0).applyState rho)
    have hp (j : Fin n) :
        (((T j.succ).applyState ((T 0).applyState rho)).vonNeumann-((T 0).applyState rho).vonNeumann)≤
          (((T j.succ).applyState rho).vonNeumann-rho.vonNeumann) := by
      have hd := QIT.State.relativeEntropy_dataProcessing_channel_ge rho ((T j.succ).applyState rho) (T 0)
      rw [hcomm 0 j.succ rho,hgain j.succ rho,hgain j.succ ((T 0).applyState rho)] at hd
      exact_mod_cast hd
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hp j)
    rw [channelRun,QIT.Channel.applyState_comp,Fin.sum_univ_succ]
    change ((channelRun n (fun j => T j.succ)).applyState ((T 0).applyState rho)).vonNeumann-rho.vonNeumann≤_
    linarith

theorem pinchingState_channels_commute (C D : Matrix a a ℂ)
    (hC : C.conjTranspose=C ∧ C*C=1) (hD : D.conjTranspose=D ∧ D*D=1) (hc : Commute C D)
    (rho : QIT.State a) :
    pinchingState C hC (pinchingState D hD rho)=pinchingState D hD (pinchingState C hC rho) := by
  apply QIT.State.ext
  have he : C*(D*rho.matrix*D)*C=D*(C*rho.matrix*C)*D := by
    calc
      _=(C*D)*rho.matrix*(D*C) := by simp only [Matrix.mul_assoc]
      _=(D*C)*rho.matrix*(C*D) := by rw [hc.eq]
      _=_ := by simp only [Matrix.mul_assoc]
  simp only [pinchingState_matrix,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_add,Matrix.add_mul,smul_add]
  rw [he]
  module

theorem commuting_pinching_entropy (n : Nat) (C : Fin n → Matrix a a ℂ)
    (hC : ∀ i, (C i).conjTranspose=C i ∧ C i*C i=1) (hc : ∀ i j, Commute (C i) (C j)) (rho : QIT.State a) :
    ((channelRun n (fun i => pinchingChannel (C i) (hC i))).applyState rho).vonNeumann-rho.vonNeumann≤
      ∑ i, ((pinchingState (C i) (hC i) rho).vonNeumann-rho.vonNeumann) := by
  apply channelRun_entropy
  · intro i sigma
    exact pinching_relativeEntropy (C i) (hC i) sigma
  · intro i j sigma
    exact pinchingState_channels_commute (C i) (C j) (hC i) (hC j) (hc i j) sigma

theorem commuting_pinching_factor_bound {b : Type*} [Fintype b] [DecidableEq b]
    (n : Nat) (C : Fin n → Matrix a a ℂ) (hC : ∀ i, (C i).conjTranspose=C i ∧ C i*C i=1)
    (hc : ∀ i j, Commute (C i) (C j)) (K : Matrix a b ℂ) (hK : hsNorm K=1)
    (Z : Fin n → Matrix.unitaryGroup b ℂ) (e : Fin n → ℝ) (he0 : ∀ i, 0≤e i)
    (he : ∀ i, hsNorm (K*(Z i:Matrix b b ℂ)-C i*K)≤e i) :
    ((channelRun n (fun i => pinchingChannel (C i) (hC i))).applyState (factorState K hK)).vonNeumann≤
      (factorState K hK).vonNeumann+∑ i, binaryEntropy (min ((e i)^2/4) (1/2)) := by
  have h := commuting_pinching_entropy n C hC hc (factorState K hK)
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => pinching_factor_bound (C i) (hC i) K hK (Z i) (e i) (he0 i) (he i))
  linarith

end
end Companion.Analytic.CountProof
