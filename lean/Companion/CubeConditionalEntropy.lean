import Companion.BinaryConditionalEntropy

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 600000

def cubeEntropy {n : Nat} (p : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ g, Real.negMulLog (p g))/Real.log 2

/-- H(bit i | all the other bits), expressed without a choice of ordering
on the remaining coordinates. Each unordered pair occurs twice. -/
def cubeConditional {n : Nat} (p : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  (∑ g, binaryMassEntropy (p g) (p (flip g i)))/2

theorem cube_sum_cons {A : Type*} [AddCommMonoid A] {n : Nat}
    (f : (Fin (n+1) → Bool) → A) :
    (∑ g, f g)=(∑ g : Fin n → Bool, f (Fin.cons false g))+
      ∑ g : Fin n → Bool, f (Fin.cons true g) := by
  rw [sum_cube_succ]
  simp [add_comm]

theorem flip_cons_zero {n : Nat} (b : Bool) (g : Fin n → Bool) :
    flip (Fin.cons b g) 0=Fin.cons (!b) g := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [flip]

theorem flip_cons_succ {n : Nat} (b : Bool) (g : Fin n → Bool) (i : Fin n) :
    flip (Fin.cons b g) i.succ=Fin.cons b (flip g i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [flip,Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · simp [flip,Function.update_apply]

theorem cubeConditional_zero {n : Nat} (p : (Fin (n+1) → Bool) → ℝ) (hp : ∀ g, 0≤p g) :
    cubeConditional p 0=∑ g : Fin n → Bool,
      binaryMassEntropy (p (Fin.cons false g)) (p (Fin.cons true g)) := by
  rw [cubeConditional,cube_sum_cons]
  simp only [flip_cons_zero,Bool.not_false,Bool.not_true]
  have hs : (∑ g : Fin n → Bool, binaryMassEntropy (p (Fin.cons true g)) (p (Fin.cons false g)))=
      ∑ g : Fin n → Bool, binaryMassEntropy (p (Fin.cons false g)) (p (Fin.cons true g)) := by
    apply Finset.sum_congr rfl
    intro g _
    exact binaryMassEntropy_symm _ _ (hp _) (hp _)
  rw [hs]
  ring

/-- The exact finite Shannon chain rule, including zero probability cells. -/
theorem cubeEntropy_chain {n : Nat} (p : (Fin (n+1) → Bool) → ℝ) (hp : ∀ g, 0≤p g) :
    cubeEntropy p=cubeEntropy (fun g => p (Fin.cons false g)+p (Fin.cons true g))+
      cubeConditional p 0 := by
  rw [cubeEntropy,cube_sum_cons,cubeConditional_zero p hp]
  simp_rw [binaryMassEntropy_log _ _ (hp _) (hp _)]
  rw [← Finset.sum_div]
  unfold cubeEntropy
  rw [← add_div]
  congr 1
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

/-- Summing out one of the conditioning bits increases conditional
entropy. The proof is the binary perspective-concavity inequality. -/
theorem cubeConditional_marginal {n : Nat} (p : (Fin (n+1) → Bool) → ℝ)
    (hp : ∀ g, 0≤p g) (i : Fin n) :
    cubeConditional p i.succ≤
      cubeConditional (fun g => p (Fin.cons false g)+p (Fin.cons true g)) i := by
  unfold cubeConditional
  rw [cube_sum_cons,← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro g _
  simp only [flip_cons_succ]
  exact binaryMassEntropy_superadd _ _ _ _ (hp _) (hp _) (hp _) (hp _)

/-- The finite conditional-entropy inequality used in Step 4:
H(p) is at least the sum of H(bit i | all other bits). -/
theorem cubeEntropy_ge_sum_conditionals (n : Nat) (p : (Fin n → Bool) → ℝ)
    (hp : ∀ g, 0≤p g) (hpsum : ∑ g, p g=1) :
    (∑ i, cubeConditional p i)≤cubeEntropy p := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
    have h : ∀ g, p g=1 := by
      intro g
      have he : (∑ h : Fin 0 → Bool, p h)=p g := by
        calc
          _=∑ _h : Fin 0 → Bool, p g := Finset.sum_congr rfl (fun h _ => congrArg p (Subsingleton.elim h g))
          _=p g := by simp
      exact he.symm.trans hpsum
    unfold cubeEntropy
    simp_rw [h]
    simp
  | succ n ih =>
    let q : (Fin n → Bool) → ℝ := fun g => p (Fin.cons false g)+p (Fin.cons true g)
    have hq : ∀ g, 0≤q g := fun g => add_nonneg (hp _) (hp _)
    have hqs : ∑ g, q g=1 := by
      rw [cube_sum_cons] at hpsum
      simpa only [q,Finset.sum_add_distrib] using hpsum
    have hi := ih q hq hqs
    have hm := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => cubeConditional_marginal p hp i)
    rw [Fin.sum_univ_succ,cubeEntropy_chain p hp]
    simpa only [add_comm] using add_le_add_left (hm.trans hi) (cubeConditional p 0)

/-- The Hellinger estimate for each conditional bit, with the exact
one-half coefficient of the full-cube squared distance. -/
theorem cubeConditional_hellinger {n : Nat} (p : (Fin n → Bool) → ℝ)
    (hp : ∀ g, 0≤p g) (hpsum : ∑ g, p g=1) (i : Fin n) :
    1-(∑ g, (Real.sqrt (p g)-Real.sqrt (p (flip g i)))^2)/(2*Real.log 2)≤
      cubeConditional p i := by
  have hi : (∑ g, p (flip g i))=1 := by
    have he : Function.Involutive (fun g : Fin n → Bool => flip g i) := fun g => flip_flip g i
    exact (Fintype.sum_equiv (he.toPerm (fun g => flip g i)) _ p (fun _ => rfl)).trans hpsum
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (fun g _ => binaryMassEntropy_hellinger (p g) (p (flip g i)) (hp _) (hp _))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,hpsum,hi] at h
  rw [← Finset.sum_div] at h
  unfold cubeConditional
  have hf : (∑ g, (Real.sqrt (p g)-Real.sqrt (p (flip g i)))^2)/(2*Real.log 2)=
      ((∑ g, (Real.sqrt (p g)-Real.sqrt (p (flip g i)))^2)/Real.log 2)/2 := by ring
  rw [hf]
  linarith

end
end Companion.Analytic.CountProof
