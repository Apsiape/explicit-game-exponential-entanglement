import Companion.BlockEntropyLower

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

variable {a : Type*} [Fintype a] [DecidableEq a]

omit [Fintype a] in
theorem symmetryProjection_sum (C : Matrix a a ℂ) :
    symmetryProjection C false+symmetryProjection C true=1 := by
  simp only [symmetryProjection,Bool.false_eq_true,↓reduceIte]
  module

theorem commute_symmetryProjection (D C : Matrix a a ℂ) (hc : Commute D C) (s : Bool) :
    Commute D (symmetryProjection C s) := by
  change D*symmetryProjection C s=symmetryProjection C s*D
  cases s <;> simp [symmetryProjection,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,hc.eq]

/-- The actual ordered joint spectral projections. The order also agrees
with the Kraus operators of the sequential pinching channels. -/
def jointProjection : (n : Nat) → (Fin n → Matrix a a ℂ) → (Fin n → Bool) → Matrix a a ℂ
  | 0,_,_ => 1
  | n+1,C,g => jointProjection n (Fin.tail C) (Fin.tail g)*symmetryProjection (C 0) (g 0)

theorem jointProjection_commute (n : Nat) (C : Fin n → Matrix a a ℂ)
    (D : Matrix a a ℂ) (hc : ∀ i, Commute D (C i)) (g : Fin n → Bool) :
    Commute D (jointProjection n C g) := by
  induction n with
  | zero => exact Commute.one_right D
  | succ n ih =>
    exact (ih (Fin.tail C) (fun i => hc i.succ) (Fin.tail g)).mul_right
      (commute_symmetryProjection D (C 0) (hc 0) (g 0))

theorem jointProjection_hermitian (n : Nat) (C : Fin n → Matrix a a ℂ)
    (hC : ∀ i, (C i).conjTranspose=C i) (hc : ∀ i j, Commute (C i) (C j)) (g : Fin n → Bool) :
    (jointProjection n C g).conjTranspose=jointProjection n C g := by
  induction n with
  | zero => simp [jointProjection]
  | succ n ih =>
    have ht := ih (Fin.tail C) (fun i => hC i.succ) (fun i j => hc i.succ j.succ) (Fin.tail g)
    have hm := jointProjection_commute n (Fin.tail C) (symmetryProjection (C 0) (g 0))
      (fun i => (commute_symmetryProjection (C i.succ) (C 0) (hc i.succ 0) (g 0)).symm) (Fin.tail g)
    rw [jointProjection,Matrix.conjTranspose_mul,ht,symmetryProjection_hermitian _ (hC 0)]
    exact hm.eq

theorem jointProjection_complete (n : Nat) (C : Fin n → Matrix a a ℂ)
    (hC : ∀ i, (C i).conjTranspose=C i ∧ C i*C i=1) :
    (∑ g, (jointProjection n C g).conjTranspose*jointProjection n C g)=1 := by
  induction n with
  | zero => simp [jointProjection]
  | succ n ih =>
    rw [sum_cube_succ]
    have ht := ih (Fin.tail C) (fun i => hC i.succ)
    have he (b : Bool) :
        (∑ g : Fin n → Bool, (jointProjection (n+1) C (Fin.cons b g)).conjTranspose*
          jointProjection (n+1) C (Fin.cons b g))=
        (symmetryProjection (C 0) b).conjTranspose*symmetryProjection (C 0) b := by
      simp only [jointProjection,Fin.tail_cons,Fin.cons_zero,Matrix.conjTranspose_mul]
      calc
        _=(symmetryProjection (C 0) b).conjTranspose*
            (∑ g : Fin n → Bool, (jointProjection n (Fin.tail C) g).conjTranspose*
              jointProjection n (Fin.tail C) g)*symmetryProjection (C 0) b := by
          simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
        _=_ := by rw [ht,Matrix.mul_one]
    simp_rw [he]
    exact symmetryProjection_complete (C 0) (hC 0)

theorem channelRun_jointProjection (n : Nat) (C : Fin n → Matrix a a ℂ)
    (hC : ∀ i, (C i).conjTranspose=C i ∧ C i*C i=1) (X : Matrix a a ℂ) :
    (channelRun n (fun i => pinchingChannel (C i) (hC i))).map X=
      ∑ g, jointProjection n C g*X*(jointProjection n C g).conjTranspose := by
  induction n generalizing X with
  | zero => simp [channelRun,jointProjection,QIT.Channel.idChannel,QIT.MatrixMap.ofKraus]
  | succ n ih =>
    rw [channelRun]
    change (channelRun n (fun i => pinchingChannel (C i.succ) (hC i.succ))).map
      (∑ b : Bool, symmetryProjection (C 0) b*X*(symmetryProjection (C 0) b).conjTranspose)=_
    rw [ih]
    rw [sum_cube_succ,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    simp only [jointProjection,Fin.tail_cons,Fin.cons_zero,Matrix.conjTranspose_mul,
      Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc,Fin.tail_def,Fin.cons_succ]

end
end Companion.Analytic.CountProof
