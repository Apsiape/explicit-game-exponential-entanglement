import Companion.CountTheorem

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

theorem sum_filter_sq_le (n : Nat) (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → ℝ) (k : ℝ) (hf0 : ∀ j, 0≤f j) (hf : ∀ j, p j → f j≤k) :
    (∑ j ∈ Finset.univ.filter p, (f j)^2)≤(n:ℝ)*k^2 := by
  rw [Finset.sum_filter]
  calc
    _≤∑ _j : Fin n, k^2 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : p j
      · simp only [hj,↓reduceIte]
        exact pow_le_pow_left₀ (hf0 j) (hf j hj) 2
      · simp only [hj,↓reduceIte]; exact sq_nonneg k
    _=_ := by simp

theorem uniform_aSquared {M d : Nat} (_X Z : Fin M → Mat d) (s : State d) (k : ℝ)
    (hZ : ∀ i, IsInvolution (Z i))
    (hZZ : ∀ i j, i≠j → hs (comm (Z i) (Z j)*s.xi)≤k)
    (hcZ : ∀ i, hs (comm (Z i) s.xi)≤k) (i : Fin M) :
    aSquared Z s i≤10*(M:ℝ)*k^2 := by
  have h1 := sum_filter_sq_le M (fun j => i<j)
    (fun j => hs (comm (Z i) (Z j)*s.xi)+hs (comm (Z j) s.xi)) (2*k)
    (fun j => add_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))
    (fun j hj => by have hp:=hZZ i j (ne_of_lt hj); have hs:=hcZ j; linarith)
  have h2 := sum_filter_sq_le M (fun j => i<j)
    (fun j => hs (comm (Z j) s.xi)) k (fun j => hsNorm_nonneg _) (fun j _ => hcZ j)
  have h := count_a_bound Z s hZ i
  nlinarith

theorem uniform_bSquared {M d : Nat} (X Z : Fin M → Mat d) (s : State d) (k : ℝ)
    (hX : ∀ i, IsInvolution (X i)) (hZ : ∀ i, IsInvolution (Z i))
    (hXZ : ∀ i j, i≠j → hs (comm (X i) (Z j)*s.xi)≤k)
    (ha : ∀ i, hs (anti (X i) (Z i)*s.xi)≤k)
    (hcZ : ∀ i, hs (comm (Z i) s.xi)≤k) (i : Fin M) :
    bSquared X Z s i≤10*(M:ℝ)*k^2 := by
  let f := fun j => if j=i then hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi) else
    hs (comm (X i) (Z j)*s.xi)+hs (comm (Z j) s.xi)
  have hf0 : ∀ j, 0≤f j := by
    intro j; dsimp [f]; split <;> exact add_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  have hf : ∀ j, f j≤2*k := by
    intro j
    by_cases hj : j=i
    · simp only [f,hj,↓reduceIte]
      have h1:=ha i; have h2:=hcZ i; linarith
    · simp only [f,hj,↓reduceIte]
      have h1:=hXZ i j (Ne.symm hj); have h2:=hcZ j; linarith
  have h1 : (hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi))^2+
      (∑ j ∈ Finset.univ.filter (fun j => j≠i),
        (hs (comm (X i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2)≤(M:ℝ)*(2*k)^2 := by
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => pow_le_pow_left₀ (hf0 j) (hf j) 2)
    have he : (∑ j, (f j)^2)=(hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi))^2+
        ∑ j ∈ Finset.univ.filter (fun j => j≠i),
          (hs (comm (X i) (Z j)*s.xi)+hs (comm (Z j) s.xi))^2 := by
      simp_rw [f,ite_pow]
      exact sum_single_piece i _ _
    rw [he] at h
    simpa only [← hs_eq_hsNorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h
  have h2 : (∑ j, hs (comm (Z j) s.xi)^2)≤(M:ℝ)*k^2 := by
    have h := Finset.sum_le_sum (s:=Finset.univ)
      (fun j _ => pow_le_pow_left₀ (hsNorm_nonneg _) (hcZ j) 2)
    simpa only [← hs_eq_hsNorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h
  have h := count_b_bound X Z s hX hZ i
  nlinarith

theorem uniform_augmented_error (M : Nat) (hM : 2≤M) (a c k : ℝ)
    (ha0 : 0≤a) (ha : a≤10*(M:ℝ)*k^2) (hc0 : 0≤c) (hc : c≤k) :
    (Real.sqrt a+c)^2≤16*(M:ℝ)*k^2 := by
  have hM2 : (2:ℝ)≤M := by exact_mod_cast hM
  have hc2 : c^2≤k^2 := pow_le_pow_left₀ hc0 hc 2
  have hs := Real.sq_sqrt ha0
  have h := sq_nonneg (Real.sqrt a-3*c)
  have hm := mul_nonneg (sub_nonneg.mpr hM2) (sq_nonneg k)
  nlinarith

end
end Companion.Analytic.CountProof
