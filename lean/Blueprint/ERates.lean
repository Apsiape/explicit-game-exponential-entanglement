import Blueprint.RatesDefinitions
import Blueprint.MixedStates
import Mathlib.Analysis.Convex.Jensen
import Blueprint.W2.CHSHBookkeeping
import Blueprint.W2.CHSHTriples
import Blueprint.W2.CliffordMatrices
import Blueprint.W2.CHSHExact
import Blueprint.W2.CHSHCollision
import Blueprint.W2.CHSHPairBounds
import Blueprint.W2.CHSHOptimize
import Blueprint.W2.CHSHSelection

namespace Blueprint.ERates
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def lambdaTriple {d : Nat} (A : Fin 3 → Mat d) (s : State d) : ℝ :=
  hs (anti (A 0) (A 1)*s.xi)+hs (anti (A 1) (A 2)*s.xi)+hs (anti (A 0) (A 2)*s.xi)+
    ∑ i, hs (comm (A i) s.xi)
def tripleX {d : Nat} (A : Fin 3 → Mat d) : Mat d := roundUnitary (Complex.I • (A 0*A 1))
def tripleZ {d : Nat} (A : Fin 3 → Mat d) : Mat d := roundUnitary (Complex.I • (A 1*A 2))
def muTriple {d : Nat} (A B : Fin 3 → Mat d) (s : State d) : ℝ :=
  ∑ i, ∑ j, hs (anti (A i) (B j)*s.xi)

theorem alice_entropy {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (s : State a)
    (hrho : s.rho=(psi.conjTranspose*psi).transpose) :
    entropy s.rho=entropy (psi.conjTranspose*psi) := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self psi
  have hroots := congrArg Polynomial.roots
    (Matrix.charpoly_transpose (psi.conjTranspose*psi))
  rw [hH.transpose.roots_charpoly_eq_eigenvalues,
    hH.roots_charpoly_eq_eigenvalues] at hroots
  have hsum := congrArg (fun z : Multiset ℂ =>
    (z.map (fun w => Real.negMulLog w.re)).sum) hroots
  rw [hrho,entropy,entropy,dite_eq_left hH.transpose,dite_eq_left hH]
  congr 1
  simpa [Multiset.map_map,Function.comp_def,List.sum_ofFn] using hsum

theorem optimize {n a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) A B
    (hv : validCHSH (n:=n) psi A B) : ∃ (A' : Fin n → Mat a) (B' : Fin n → Fin n → Mat b),
    (∀ i, IsInvolution (A' i)) ∧ (∀ i j, i≠j → IsInvolution (B' i j)) ∧
      chshBias psi A B≤chshBias psi A' B' := by
  have hH := W2.alicePayoff_hermitian psi B (fun i j hij => (hv.2.2 i j hij).1)
  let A' := fun i => W2.payoffSign (W2.alicePayoff psi B i) (hH i)
  have hA' (i : Fin n) : IsInvolution (A' i) := W2.payoffSign_involution _ _
  let B' := W2.optimizedBob psi A' (fun i => (hA' i).1)
  have hFirst : (∑ i, ∑ j, if i<j then chshPair psi A B i j else 0)≤
      (∑ i, ∑ j, if i<j then chshPair psi A' B i j else 0) := by
    rw [←W2.alicePayoff_total,←W2.alicePayoff_total]
    exact Finset.sum_le_sum (fun i _ => W2.payoffSign_optimal _ _ (hH i) (hv.2.1 i))
  have hSecond : (∑ i, ∑ j, if i<j then chshPair psi A' B i j else 0)≤
      (∑ i, ∑ j, if i<j then chshPair psi A' B' i j else 0) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split
    · exact W2.optimizedBob_pair psi A' B (fun i => (hA' i).1) hv.2.2 i j ‹_›
    · exact le_rfl
  refine ⟨A',B',hA',fun i j _ => W2.optimizedBob_involution psi A' (fun i => (hA' i).1) i j,?_⟩
  exact div_le_div_of_nonneg_right (hFirst.trans hSecond) (by positivity)

theorem one_pair {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1)
    (A A' : Mat a) (B B' : Mat b) (hA : IsInvolution A) (hA' : IsInvolution A')
    (hB : IsInvolution B) (hB' : IsInvolution B') (s : State a)
    (hrho : s.rho=(psi.conjTranspose*psi).transpose) :
    let C := expectation psi A (B+B')+expectation psi A' (B-B')
    let delta := 2*Real.sqrt 2-C
    delta=(hs (((1/Real.sqrt 2:ℝ):ℂ) • ((B+B')*psi)-psi*A.transpose)^2+
      hs (((1/Real.sqrt 2:ℝ):ℂ) • ((B-B')*psi)-psi*A'.transpose)^2)/Real.sqrt 2 ∧
    0≤delta ∧ hs (anti A A'*s.xi)^2≤33*delta ∧
      hs (comm A s.xi)^2≤2*Real.sqrt 2*delta ∧ hs (comm A' s.xi)^2≤2*Real.sqrt 2*delta := by
  dsimp only
  let delta := 2*Real.sqrt 2-(expectation psi A (B+B')+expectation psi A' (B-B'))
  let E := (((1/Real.sqrt 2:ℝ):ℂ) • ((B+B')*psi)-psi*A.transpose)
  let E' := (((1/Real.sqrt 2:ℝ):ℂ) • ((B-B')*psi)-psi*A'.transpose)
  have hsum : hs E^2+hs E'^2=Real.sqrt 2*delta := by
    simpa only [E,E',delta,W2.chshPlus,Matrix.smul_mul,←sub_eq_add_neg] using
      W2.pair_sum_squares psi hp A A' B B' hA hA' hB hB'
  have hroot : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hd : 0≤delta := (mul_nonneg_iff_of_pos_left hroot).mp (by rw [←hsum]; positivity)
  have hlin := W2.pair_anti_linear psi A A' B B' hA hA' hB hB'
  rw [←W2.alice_weighted_norm psi s hrho (anti A A')] at hlin
  simp only [W2.chshPlus,Matrix.smul_mul,←sub_eq_add_neg] at hlin
  change hs (anti A A'*s.xi)≤(1+Real.sqrt 2)*(hs E+hs E') at hlin
  have hsq := pow_le_pow_left₀ (hsNorm_nonneg (anti A A'*s.xi)) hlin 2
  have hcs : (hs E+hs E')^2≤2*(hs E^2+hs E'^2) := by nlinarith [sq_nonneg (hs E-hs E')]
  have hcoef : 2*(1+Real.sqrt 2)^2*Real.sqrt 2≤(33:ℝ) := by
    have hroot2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hroot3 := congrArg (fun r : ℝ => r*Real.sqrt 2) hroot2
    nlinarith
  have hanti : hs (anti A A'*s.xi)^2≤33*delta := by
    calc
      _≤((1+Real.sqrt 2)*(hs E+hs E'))^2 := hsq
      _≤2*(1+Real.sqrt 2)^2*(hs E^2+hs E'^2) := by
        nlinarith only [mul_le_mul_of_nonneg_left hcs (sq_nonneg (1+Real.sqrt 2))]
      _=(2*(1+Real.sqrt 2)^2*Real.sqrt 2)*delta := by rw [hsum]; ring
      _≤33*delta := mul_le_mul_of_nonneg_right hcoef hd
  have hT : (W2.chshPlus B B').IsHermitian := by
    simp [W2.chshPlus,Matrix.IsHermitian,Matrix.conjTranspose_smul,hB.1,hB'.1]
  have hT' : (W2.chshPlus B (-B')).IsHermitian := by
    simp [W2.chshPlus,Matrix.IsHermitian,Matrix.conjTranspose_smul,hB.1,hB'.1]
  have hc := W2.state_pair_consistency psi A _ hA.1 hT s hrho
  have hc' := W2.state_pair_consistency psi A' _ hA'.1 hT' s hrho
  simp only [W2.chshPlus,Matrix.smul_mul,←sub_eq_add_neg] at hc hc'
  change hs (comm A s.xi)^2≤2*hs E^2 at hc
  change hs (comm A' s.xi)^2≤2*hs E'^2 at hc'
  refine ⟨?_,hd,hanti,?_,?_⟩
  · change delta=(hs E^2+hs E'^2)/Real.sqrt 2
    apply (eq_div_iff (ne_of_gt hroot)).mpr
    nlinarith only [hsum]
  · change hs (comm A s.xi)^2≤2*Real.sqrt 2*delta
    nlinarith [sq_nonneg (hs E')]
  · change hs (comm A' s.xi)^2≤2*Real.sqrt 2*delta
    nlinarith [sq_nonneg (hs E)]

theorem subset_triples (n M : Nat) (hM : 1≤M) (hn : 3*M≤n)
    (delta : Fin n → Fin n → ℝ) (hd : ∀ i j, 0≤delta i j)
    (hsym : ∀ i j, delta i j=delta j i) (eps : ℝ)
    (hb : (∑ i, ∑ j, if i<j then delta i j else 0)≤2*Real.sqrt 2*eps*(n.choose 2)) :
    ∃ f : (Fin M × Fin 3) ↪ Fin n,
      (∑ x, ∑ y, if f x<f y then delta (f x) (f y) else 0)≤
        2*Real.sqrt 2*eps*((3*M).choose 2) ∧
      (∑ k, ∑ r : Fin 3, ∑ s : Fin 3, if r<s then delta (f (k,r)) (f (k,s)) else 0)≤
        2*Real.sqrt 2*eps*(3*M) := by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    W2.select_triples n M hM hn delta hsym (2*Real.sqrt 2*eps) hb

theorem deficit_budget {n a b : Nat} (hn : 2≤n) (psi : Matrix (Fin b) (Fin a) ℂ)
    (hp : hs psi=1) (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b)
    (hA : ∀ i, IsInvolution (A i)) (hB : ∀ i j, i≠j → IsInvolution (B i j))
    (eps : ℝ) (hb : (1-eps)*optimalBias≤chshBias psi A B) :
    (∀ i j, i<j → 0≤2*Real.sqrt 2-chshPair psi A B i j) ∧
      (∑ i, ∑ j, if i<j then 2*Real.sqrt 2-chshPair psi A B i j else 0)≤
        2*Real.sqrt 2*eps*(n.choose 2) := by
  have hPair (i j : Fin n) (hij : i<j) : 0≤2*Real.sqrt 2-chshPair psi A B i j := by
    have ho := one_pair psi hp (A i) (A j) (B i j) (B j i)
      (hA i) (hA j) (hB i j (ne_of_lt hij)) (hB j i (ne_of_gt hij))
      (W2.aliceState psi hp) (W2.aliceState_rho psi hp)
    exact ho.2.1
  refine ⟨hPair,?_⟩
  have hsplit (i j : Fin n) :
      (if i<j then 2*Real.sqrt 2-chshPair psi A B i j else 0)=
      (2*Real.sqrt 2)*(if i<j then 1 else 0)-(if i<j then chshPair psi A B i j else 0) := by
    split <;> ring
  simp_rw [hsplit,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [W2.pair_count,W2.choose_two_cast]
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hpred : (0:ℝ)<(n-1:Nat) := by exact_mod_cast (by omega : 0<n-1)
  have hden : (0:ℝ)<2*n*(n-1:Nat) := by positivity
  have hb' := (le_div_iff₀ hden).mp hb
  unfold optimalBias at hb'
  nlinarith only [hb']

theorem selected_error_sums {n M d : Nat} (hM : 1≤M) (A : Fin n → Mat d) (s : State d)
    (f : (Fin M × Fin 3) ↪ Fin n) (delta : Fin n → Fin n → ℝ) (bar : ℝ)
    (hd : ∀ i j, 0≤delta i j) (hsym : ∀ i j, delta i j=delta j i)
    (hanti : ∀ i j, i≠j → hs (anti (A i) (A j)*s.xi)^2≤33*delta i j)
    (hc : ∀ i j, i≠j → hs (comm (A i) s.xi)^2≤2*Real.sqrt 2*delta i j)
    (hsel : (∑ x, ∑ y, if f x<f y then delta (f x) (f y) else 0)≤((3*M).choose 2)*bar)
    (hint : (∑ k, ∑ r : Fin 3, ∑ t : Fin 3, if r<t then delta (f (k,r)) (f (k,t)) else 0)≤(3*M:Nat)*bar) :
    (∑ k, lambdaTriple (fun r => A (f (k,r))) s^2)≤215*(3*M:Nat)*bar ∧
    (∑ k, ∑ l, if k≠l then muTriple (fun r => A (f (k,r))) (fun r => A (f (l,r))) s^2 else 0)≤
      297*(3*M:Nat)^2*bar := by
  classical
  have hne (k : Fin M) (r t : Fin 3) (h : r≠t) : f (k,r)≠f (k,t) :=
    f.injective.ne (fun heq => h (congrArg Prod.snd heq))
  have htriple (k : Fin M) :
      lambdaTriple (fun r => A (f (k,r))) s^2≤215*
        (delta (f (k,0)) (f (k,1))+delta (f (k,0)) (f (k,2))+delta (f (k,1)) (f (k,2))) := by
    let H := fun r t : Fin 3 => hs (anti (A (f (k,r))) (A (f (k,t)))*s.xi)
    let C := fun r : Fin 3 => hs (comm (A (f (k,r))) s.xi)
    let D := delta (f (k,0)) (f (k,1))+delta (f (k,0)) (f (k,2))+delta (f (k,1)) (f (k,2))
    have hD : 0≤D := add_nonneg (add_nonneg (hd _ _) (hd _ _)) (hd _ _)
    have ha01 := hanti _ _ (hne k 0 1 (by decide))
    have ha02 := hanti _ _ (hne k 0 2 (by decide))
    have ha12 := hanti _ _ (hne k 1 2 (by decide))
    have hc01 := hc _ _ (hne k 0 1 (by decide))
    have hc02 := hc _ _ (hne k 0 2 (by decide))
    have hc10 := hc _ _ (hne k 1 0 (by decide))
    have hc12 := hc _ _ (hne k 1 2 (by decide))
    have hc20 := hc _ _ (hne k 2 0 (by decide))
    have hc21 := hc _ _ (hne k 2 1 (by decide))
    rw [hsym (f (k,1)) (f (k,0))] at hc10
    rw [hsym (f (k,2)) (f (k,0))] at hc20
    rw [hsym (f (k,2)) (f (k,1))] at hc21
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ)
      (f:=fun _ : Fin 6 => (1:ℝ)) (g:=![H 0 1,H 1 2,H 0 2,C 0,C 1,C 2])
    norm_num [Fin.sum_univ_succ] at hcs
    have hlambda : lambdaTriple (fun r => A (f (k,r))) s=
        H 0 1+H 1 2+H 0 2+C 0+C 1+C 2 := by
      simp [lambdaTriple,H,C,Fin.sum_univ_succ]
      ring
    have hstep : lambdaTriple (fun r => A (f (k,r))) s^2≤6*(33+2*Real.sqrt 2)*D := by
      rw [hlambda]
      dsimp [H,C,D] at hcs ⊢
      nlinarith only [hcs,ha01,ha02,ha12,hc01,hc02,hc10,hc12,hc20,hc21]
    have hcoef : 6*(33+2*Real.sqrt 2)≤215 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    exact hstep.trans (mul_le_mul_of_nonneg_right hcoef hD)
  have hint' : (∑ k, (delta (f (k,0)) (f (k,1))+delta (f (k,0)) (f (k,2))+
      delta (f (k,1)) (f (k,2))))≤(3*M:Nat)*bar := by
    simpa [Fin.sum_univ_succ,add_assoc] using hint
  have hbar : 0≤bar := by
    have hnonneg : 0≤∑ k, (delta (f (k,0)) (f (k,1))+delta (f (k,0)) (f (k,2))+
      delta (f (k,1)) (f (k,2))) :=
      Finset.sum_nonneg (fun k _ => add_nonneg (add_nonneg (hd _ _) (hd _ _)) (hd _ _))
    exact nonneg_of_mul_nonneg_right (hnonneg.trans hint') (by positivity : (0:ℝ)<(3*M:Nat))
  constructor
  · calc
      _≤∑ k, 215*(delta (f (k,0)) (f (k,1))+delta (f (k,0)) (f (k,2))+
          delta (f (k,1)) (f (k,2))) := Finset.sum_le_sum (fun k _ => htriple k)
      _≤215*((3*M:Nat)*bar) := by
        rw [←Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hint' (by norm_num)
      _=_ := by ring
  · let D := fun x y : Fin M × Fin 3 => delta (f x) (f y)
    let T := ∑ x : Fin M × Fin 3, ∑ y : Fin M × Fin 3, if f x<f y then D x y else 0
    have horder : (∑ x : Fin M × Fin 3, ∑ y : Fin M × Fin 3, if x≠y then D x y else 0)=2*T := by
      have hpoint (x y : Fin M × Fin 3) :
          (if x≠y then D x y else 0)=
          (if f x<f y then D x y else 0)+(if f y<f x then D y x else 0) := by
        by_cases h : x=y
        · subst y; simp
        · have hneq : f x≠f y := f.injective.ne h
          rcases lt_or_gt_of_ne hneq with hxy | hyx
          · simp [h,hxy,not_lt_of_ge hxy.le]
          · simp [h,hyx,not_lt_of_ge hyx.le,D,hsym]
      simp_rw [hpoint,Finset.sum_add_distrib]
      have hflip : (∑ x : Fin M × Fin 3, ∑ y : Fin M × Fin 3,
          if f y<f x then D y x else 0)=T := Finset.sum_comm
      rw [hflip]
      dsimp [T]
      ring
    have hmu (k l : Fin M) (hkl : k≠l) :
        muTriple (fun r => A (f (k,r))) (fun r => A (f (l,r))) s^2≤
          297*(∑ r : Fin 3, ∑ t : Fin 3, D (k,r) (l,t)) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ)
        (f:=fun _ : Fin 3 × Fin 3 => (1:ℝ))
        (g:=fun rt : Fin 3 × Fin 3 => hs (anti (A (f (k,rt.1))) (A (f (l,rt.2)))*s.xi))
      simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcs
      simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,
        Fintype.sum_prod_type] at hcs
      have hab : (∑ r : Fin 3, ∑ t : Fin 3,
          hs (anti (A (f (k,r))) (A (f (l,t)))*s.xi)^2)≤
          33*(∑ r : Fin 3, ∑ t : Fin 3, D (k,r) (l,t)) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro r _
        apply Finset.sum_le_sum
        intro t _
        exact hanti _ _ (f.injective.ne (by simp [hkl]))
      dsimp [muTriple]
      linarith
    have hexternal :
        (∑ k : Fin M, ∑ l : Fin M, if k≠l then ∑ r : Fin 3, ∑ t : Fin 3, D (k,r) (l,t) else 0)≤2*T := by
      rw [←horder]
      calc
        _=(∑ k : Fin M, ∑ l : Fin M, ∑ r : Fin 3, ∑ t : Fin 3,
            if k≠l then D (k,r) (l,t) else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          by_cases hkl : k=l <;> simp [hkl]
        _≤∑ k : Fin M, ∑ l : Fin M, ∑ r : Fin 3, ∑ t : Fin 3,
            if (k,r)≠(l,t) then D (k,r) (l,t) else 0 := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro l _
          apply Finset.sum_le_sum
          intro r _
          apply Finset.sum_le_sum
          intro t _
          by_cases hkl : k=l
          · subst l
            by_cases hrt : r=t
            · simp [hrt]
            · simpa [hrt,D] using hd (f (k,r)) (f (k,t))
          · simp [hkl,D]
        _=_ := by
          simp only [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro k _
          exact Finset.sum_comm
    have htotal : (∑ k, ∑ l, if k≠l then
        muTriple (fun r => A (f (k,r))) (fun r => A (f (l,r))) s^2 else 0)≤297*(2*T) := by
      calc
        _≤297*(∑ k : Fin M, ∑ l : Fin M,
            if k≠l then ∑ r : Fin 3, ∑ t : Fin 3, D (k,r) (l,t) else 0) := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro l _
          by_cases hkl : k=l
          · simp [hkl]
          · simp only [hkl,ne_eq,not_false_eq_true,↓reduceIte]
            exact hmu k l hkl
        _≤_ := mul_le_mul_of_nonneg_left hexternal (by norm_num)
    have hchoose : 2*(3*M).choose 2≤(3*M)^2 := by
      rw [Nat.choose_two_right]
      have hdiv := Nat.div_mul_le_self ((3*M)*(3*M-1)) 2
      have hprod := Nat.mul_le_mul_left (3*M) (Nat.sub_le (3*M) 1)
      nlinarith
    have hchooseR : (2:ℝ)*((3*M).choose 2)≤(3*M:Nat)^2 := by exact_mod_cast hchoose
    have hsel' : T≤((3*M).choose 2)*bar := hsel
    have hscaled := mul_le_mul_of_nonneg_right hchooseR hbar
    nlinarith only [htotal,hsel',hscaled]

theorem triple_bounds {d : Nat} (A : Fin 3 → Mat d) (s : State d) (hA : ∀ i, IsInvolution (A i)) :
    IsInvolution (tripleX A) ∧ IsInvolution (tripleZ A) ∧
      hs (anti (tripleX A) (tripleZ A)*s.xi)≤12*lambdaTriple A s ∧
      hs (comm (tripleX A) s.xi)≤2*lambdaTriple A s ∧
      hs (comm (tripleZ A) s.xi)≤2*lambdaTriple A s := by
  have hu (j : Fin 3) := CountProof.involution_unitary (A j) (hA j)
  have hU := W2.phase_unitary _ (ReturnProof.unitary_mul _ _ (hu 0) (hu 1))
  have hV := W2.phase_unitary _ (ReturnProof.unitary_mul _ _ (hu 1) (hu 2))
  have hX := ReturnProof.roundUnitary_involution (Complex.I • (A 0*A 1))
  have hZ := ReturnProof.roundUnitary_involution (Complex.I • (A 1*A 2))
  have hrX := W2.rounded_phase_pair (A 0) (A 1) s.xi (hA 0) (hA 1) s.xi_positive.isHermitian
  have hrZ := W2.rounded_phase_pair (A 1) (A 2) s.xi (hA 1) (hA 2) s.xi_positive.isHermitian
  have hcU := W2.phase_product_commutator (A 0) (A 1) s.xi (hu 0) (hu 1)
  have hcV := W2.phase_product_commutator (A 1) (A 2) s.xi (hu 1) (hu 2)
  have ha := W2.phase_triple_anti (A 0) (A 1) (A 2) s.xi (hA 0) (hA 1) (hA 2)
  have hr := W2.signed_pair_replacement (tripleX A) (tripleZ A)
    (Complex.I • (A 0*A 1)) (Complex.I • (A 1*A 2)) s.xi (-1)
    (by simp) (CountProof.involution_unitary _ hX) (CountProof.involution_unitary _ hZ) hU hV
  simp only [neg_one_smul,sub_neg_eq_add] at hr
  change hs (anti (tripleX A) (tripleZ A)*s.xi)≤_ at hr
  have hp01 := hsNorm_nonneg (anti (A 0) (A 1)*s.xi)
  have hp12 := hsNorm_nonneg (anti (A 1) (A 2)*s.xi)
  have hp02 := hsNorm_nonneg (anti (A 0) (A 2)*s.xi)
  have hp0 := hsNorm_nonneg (comm (A 0) s.xi)
  have hp1 := hsNorm_nonneg (comm (A 1) s.xi)
  have hp2 := hsNorm_nonneg (comm (A 2) s.xi)
  simp only [←hs_eq_hsNorm] at hp01 hp12 hp02 hp0 hp1 hp2
  refine ⟨hX,hZ,?_,?_,?_⟩ <;>
    simp only [lambdaTriple,Fin.sum_univ_succ,Fin.isValue,Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  · dsimp [tripleX,tripleZ] at hr ⊢
    simp only [anti] at *
    linarith [hrX.1,hrZ.1]
  · change hs (comm (roundUnitary (Complex.I • (A 0*A 1))) s.xi)≤_
    linarith [hrX.2]
  · change hs (comm (roundUnitary (Complex.I • (A 1*A 2))) s.xi)≤_
    linarith [hrZ.2]

theorem cross_triple_bounds {d : Nat} (A B : Fin 3 → Mat d) (s : State d)
    (hA : ∀ i, IsInvolution (A i)) (hB : ∀ i, IsInvolution (B i)) :
    let mu := ∑ i, ∑ j, hs (anti (A i) (B j)*s.xi)
    hs (comm (tripleZ A) (tripleZ B)*s.xi)≤mu+8*lambdaTriple A s+8*lambdaTriple B s ∧
    hs (comm (tripleX A) (tripleZ B)*s.xi)≤mu+8*lambdaTriple A s+8*lambdaTriple B s := by
  dsimp only
  have huA (j : Fin 3) := CountProof.involution_unitary (A j) (hA j)
  have huB (j : Fin 3) := CountProof.involution_unitary (B j) (hB j)
  have one (p q : Fin 3) (hpq : (p=0 ∧ q=1) ∨ (p=1 ∧ q=2)) :
      hs (comm (roundUnitary (Complex.I • (A p*A q))) (tripleZ B)*s.xi)≤
        (∑ i, ∑ j, hs (anti (A i) (B j)*s.xi))+8*lambdaTriple A s+8*lambdaTriple B s := by
    let U := Complex.I • (A p*A q)
    let V := Complex.I • (B 1*B 2)
    have hU := W2.phase_unitary _ (ReturnProof.unitary_mul _ _ (huA p) (huA q))
    have hV := W2.phase_unitary _ (ReturnProof.unitary_mul _ _ (huB 1) (huB 2))
    have hP := ReturnProof.roundUnitary_involution U
    have hQ := ReturnProof.roundUnitary_involution V
    have hrP := W2.rounded_phase_pair (A p) (A q) s.xi (hA p) (hA q) s.xi_positive.isHermitian
    have hrQ := W2.rounded_phase_pair (B 1) (B 2) s.xi (hB 1) (hB 2) s.xi_positive.isHermitian
    have hcP := W2.phase_product_commutator (A p) (A q) s.xi (huA p) (huA q)
    have hcQ := W2.phase_product_commutator (B 1) (B 2) s.xi (huB 1) (huB 2)
    have hraw := W2.phase_cross_commutator (A p) (A q) (B 1) (B 2) s.xi
      (huA p) (huA q) (huB 1) (huB 2)
    have hr := W2.signed_pair_replacement (roundUnitary U) (roundUnitary V) U V s.xi 1
      (by simp) (CountProof.involution_unitary _ hP) (CountProof.involution_unitary _ hQ) hU hV
    simp only [one_smul] at hr
    change hs (comm (roundUnitary U) (roundUnitary V)*s.xi)≤_ at hr
    dsimp [U,V,tripleZ] at hr ⊢
    simp only [Companion.Analytic.comm] at hraw
    rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp only [lambdaTriple,Fin.sum_univ_succ,Fin.isValue,Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two,Finset.univ_eq_empty,Finset.sum_empty,add_zero] <;>
      simp only [hs_eq_hsNorm,Companion.Analytic.comm] at * <;>
      linarith [hrP.1,hrQ.1,
        hsNorm_nonneg (anti (A 0) (A 1)*s.xi),hsNorm_nonneg (anti (A 1) (A 2)*s.xi),
        hsNorm_nonneg (anti (A 0) (A 2)*s.xi),hsNorm_nonneg (anti (B 0) (B 1)*s.xi),
        hsNorm_nonneg (anti (B 1) (B 2)*s.xi),hsNorm_nonneg (anti (B 0) (B 2)*s.xi),
        hsNorm_nonneg (A 0*s.xi-s.xi*A 0),hsNorm_nonneg (A 1*s.xi-s.xi*A 1),hsNorm_nonneg (A 2*s.xi-s.xi*A 2),
        hsNorm_nonneg (B 0*s.xi-s.xi*B 0),hsNorm_nonneg (B 1*s.xi-s.xi*B 1),hsNorm_nonneg (B 2*s.xi-s.xi*B 2),
        hsNorm_nonneg (anti (A 0) (B 0)*s.xi),hsNorm_nonneg (anti (A 0) (B 1)*s.xi),
        hsNorm_nonneg (anti (A 0) (B 2)*s.xi),hsNorm_nonneg (anti (A 1) (B 0)*s.xi),
        hsNorm_nonneg (anti (A 1) (B 1)*s.xi),hsNorm_nonneg (anti (A 1) (B 2)*s.xi),
        hsNorm_nonneg (anti (A 2) (B 0)*s.xi),hsNorm_nonneg (anti (A 2) (B 1)*s.xi),
        hsNorm_nonneg (anti (A 2) (B 2)*s.xi)]
  exact ⟨one 1 2 (Or.inr ⟨rfl,rfl⟩),one 0 1 (Or.inl ⟨rfl,rfl⟩)⟩

theorem count_error_budget {M d : Nat} (hM : 1≤M) (X Z : Fin M → Mat d) (s : State d)
    (lambda : Fin M → ℝ) (mu : Fin M → Fin M → ℝ) (barDelta : ℝ)
    (hl : ∀ i, 0≤lambda i) (hm : ∀ i j, 0≤mu i j)
    (hX : ∀ i, IsInvolution (X i)) (hZ : ∀ i, IsInvolution (Z i))
    (hcZ : ∀ i j, i≠j → hs (comm (Z i) (Z j)*s.xi)≤mu i j+8*lambda i+8*lambda j)
    (hcX : ∀ i j, i≠j → hs (comm (X i) (Z j)*s.xi)≤mu i j+8*lambda i+8*lambda j)
    (ha : ∀ i, hs (anti (X i) (Z i)*s.xi)≤12*lambda i)
    (hsX : ∀ i, hs (comm (X i) s.xi)≤2*lambda i)
    (hsZ : ∀ i, hs (comm (Z i) s.xi)≤2*lambda i)
    (hls : (∑ i, lambda i^2)≤215*(3*M:Nat)*barDelta)
    (hms : (∑ i, ∑ j, if i≠j then mu i j^2 else 0)≤297*(3*M:Nat)^2*barDelta) :
    (∑ i, (aSquared Z s i+4*lambda i^2))≤73162*(3*M:Nat)^2*barDelta ∧
    (∑ i, (bSquared X Z s i+4*lambda i^2))≤101256*(3*M:Nat)^2*barDelta := by
  classical
  let L := ∑ i, lambda i^2
  let R := fun i => ∑ j, if i≠j then mu i j^2 else 0
  have hL : 0≤L := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hM' : (1:ℝ)≤M := by exact_mod_cast hM
  have hbar : 0≤barDelta := by
    have hpos : (0:ℝ)<215*(3*M:Nat) := by positivity
    exact nonneg_of_mul_nonneg_right (hL.trans hls) hpos
  have hstates : (∑ j, hs (comm (Z j) s.xi)^2)≤4*L := by
    calc
      _≤∑ j, (2*lambda j)^2 := Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (hsNorm_nonneg _) (hsZ j) 2)
      _=4*L := by dsimp [L]; simp only [mul_pow,←Finset.mul_sum]; norm_num
  have hrow (i : Fin M) (F : Fin M → ℝ) (p : Fin M → Prop) [DecidablePred p]
      (hF0 : ∀ j, 0≤F j) (hp : ∀ j, p j → i≠j)
      (hF : ∀ j, p j → F j≤mu i j+8*lambda i+8*lambda j) :
      (∑ j ∈ Finset.univ.filter p, (F j+hs (comm (Z j) s.xi))^2)≤
        3*R i+192*(M:ℝ)*lambda i^2+300*L := by
    rw [Finset.sum_filter]
    calc
      _≤∑ j, ((if i≠j then 3*mu i j^2 else 0)+192*lambda i^2+300*lambda j^2) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : p j
        · simp only [ite_eq_left hj,ite_eq_left (hp j hj)]
          have hbound : F j+hs (comm (Z j) s.xi)≤mu i j+8*lambda i+10*lambda j := by
            have h1 := hF j hj
            have h2 := hsZ j
            linarith
          have hsq := pow_le_pow_left₀
            (add_nonneg (hF0 j) (hsNorm_nonneg _)) hbound 2
          simp only [←hs_eq_hsNorm] at hsq
          nlinarith [sq_nonneg (mu i j-8*lambda i),
            sq_nonneg (mu i j-10*lambda j),sq_nonneg (8*lambda i-10*lambda j)]
        · simp only [hj,↓reduceIte]
          split <;> positivity
      _=3*R i+192*(M:ℝ)*lambda i^2+300*L := by
        have hi : (∑ j, if i≠j then 3*mu i j^2 else 0)=3*R i := by
          dsimp [R]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          split <;> simp_all
        simp only [Finset.sum_add_distrib,hi,Finset.sum_const,Finset.card_univ,
          Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
        dsimp [L]
        ring
  have ha' (i : Fin M) : aSquared Z s i≤6*R i+384*(M:ℝ)*lambda i^2+608*L := by
    have h1 := hrow i (fun j => hs (comm (Z i) (Z j)*s.xi)) (fun j => i<j)
      (fun j => hsNorm_nonneg _) (fun j hj => ne_of_lt hj) (fun j hj => hcZ i j (ne_of_lt hj))
    have h2 : (∑ j ∈ Finset.univ.filter (fun j => i<j), hs (comm (Z j) s.xi)^2)≤4*L := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => sq_nonneg _)).trans hstates
    have h := CountProof.count_a_bound Z s hZ i
    linarith
  have hb' (i : Fin M) : bSquared X Z s i≤392*lambda i^2+
      6*R i+384*(M:ℝ)*lambda i^2+608*L := by
    have h1 := hrow i (fun j => hs (comm (X i) (Z j)*s.xi)) (fun j => j≠i)
      (fun j => hsNorm_nonneg _) (fun j hj => Ne.symm hj) (fun j hj => hcX i j (Ne.symm hj))
    have hanti : (hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi))^2≤196*lambda i^2 := by
      have hbound : hs (anti (X i) (Z i)*s.xi)+hs (comm (Z i) s.xi)≤14*lambda i := by
        have h1 := ha i
        have h2 := hsZ i
        linarith
      have h := pow_le_pow_left₀
        (add_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)) hbound 2
      simp only [←hs_eq_hsNorm] at h
      nlinarith
    have h := CountProof.count_b_bound X Z s hX hZ i
    linarith
  have hsumA := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    add_le_add_right (ha' i) (4*lambda i^2))
  have hsumB := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    add_le_add_right (hb' i) (4*lambda i^2))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsumA hsumB
  have hsmall : L≤(M:ℝ)*L := le_mul_of_one_le_left hL hM'
  have hA : (∑ i, (aSquared Z s i+4*lambda i^2))≤6*(∑ i, R i)+996*(M:ℝ)*L := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    change (∑ i, aSquared Z s i)+4*L≤_
    change 4*L+(∑ i, aSquared Z s i)≤4*L+
      (6*(∑ i, R i)+384*(M:ℝ)*L+608*((M:ℝ)*L)) at hsumA
    nlinarith
  have hB : (∑ i, (bSquared X Z s i+4*lambda i^2))≤6*(∑ i, R i)+1388*(M:ℝ)*L := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    change (∑ i, bSquared X Z s i)+4*L≤_
    change 4*L+(∑ i, bSquared X Z s i)≤4*L+
      (392*L+6*(∑ i, R i)+384*(M:ℝ)*L+608*((M:ℝ)*L)) at hsumB
    nlinarith
  have hls' := mul_le_mul_of_nonneg_left hls (by positivity : (0:ℝ)≤996*M)
  have hls'' := mul_le_mul_of_nonneg_left hls (by positivity : (0:ℝ)≤1388*M)
  have hms' := mul_le_mul_of_nonneg_left hms (by norm_num : (0:ℝ)≤6)
  change 996*(M:ℝ)*L≤_ at hls'
  change 1388*(M:ℝ)*L≤_ at hls''
  change 6*(∑ i, R i)≤_ at hms'
  push_cast at hls' hls'' hms' ⊢
  constructor
  · nlinarith [hA]
  · nlinarith [hB,mul_nonneg (sq_nonneg (M:ℝ)) hbar]

theorem cappedEntropy_concave :
    ConcaveOn ℝ (Set.Ici 0) (fun x => binaryEntropy (min x (1/2))) := by
  let g : ℝ → ℝ := fun x => min x (1/2)
  have hg : ConcaveOn ℝ (Set.Ici 0) g :=
    (concaveOn_id (convex_Ici 0)).inf (concaveOn_const (1/2) (convex_Ici 0))
  have hs : g '' Set.Ici 0 ⊆ Set.Icc 0 (1/2) := by
    rintro x ⟨y,hy,rfl⟩
    exact ⟨le_min hy (by norm_num),min_le_right _ _⟩
  have hbase := Real.strictConcave_binEntropy.concaveOn.subset
    (show Set.Icc (0:ℝ) (1/2) ⊆ Set.Icc 0 1 by intro x hx; exact ⟨hx.1,by linarith [hx.2]⟩)
    (convex_Icc 0 (1/2))
  have hb : ConcaveOn ℝ (Set.Icc 0 (1/2)) binaryEntropy := by
    refine ⟨convex_Icc 0 (1/2),?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hbase.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    have hdiv := div_le_div_of_nonneg_right hh
      (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    unfold binaryEntropy
    convert hdiv using 1 <;> ring
  have hi : g '' Set.Ici 0=Set.Icc 0 (1/2) := by
    apply Set.Subset.antisymm hs
    intro x hx
    exact ⟨x,hx.1,min_eq_left hx.2⟩
  have hb' : ConcaveOn ℝ (g '' Set.Ici 0) binaryEntropy := hi.symm ▸ hb
  exact hb'.comp hg
    (fun x hx y hy hxy => CountProof.binaryEntropy_mono_half (hs hx) (hs hy) hxy)

theorem entropy_jensen {M d : Nat} (hM : 1≤M) (X Z : Fin M → Mat d) (s : State d)
    (lambda : Fin M → ℝ) (hX : ∀ i, IsInvolution (X i)) (hZ : ∀ i, IsInvolution (Z i))
    (hcX : ∀ i, hs (comm (X i) s.xi)≤2*lambda i)
    (hcZ : ∀ i, hs (comm (Z i) s.xi)≤2*lambda i) :
    (M:ℝ)-(∑ i, (bSquared X Z s i+4*lambda i^2))/Real.log 2-
      M*binaryEntropy (min ((∑ i, (aSquared Z s i+4*lambda i^2))/(2*M)) (1/2))≤entropy s.rho := by
  have hM0 : (0:ℝ)<M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ha0 (i : Fin M) : 0≤aSquared Z s i := by unfold aSquared; positivity
  have hb0 (i : Fin M) : 0≤bSquared X Z s i := by unfold bSquared; positivity
  have aug (a c l : ℝ) (ha : 0≤a) (hc0 : 0≤c) (hc : c≤2*l) :
      (Real.sqrt a+c)^2≤2*(a+4*l^2) := by
    have hcsq := pow_le_pow_left₀ hc0 hc 2
    nlinarith [Real.sq_sqrt ha,sq_nonneg (Real.sqrt a-c)]
  have hpoint (i : Fin M) :
      1-(bSquared X Z s i+4*lambda i^2)/Real.log 2-
        binaryEntropy (min ((aSquared Z s i+4*lambda i^2)/2) (1/2))≤
      1-(Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2/(2*Real.log 2)-
        binaryEntropy (min ((Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4) (1/2)) := by
    have ha := aug _ _ _ (ha0 i) (hsNorm_nonneg _) (hcZ i)
    have hb := aug _ _ _ (hb0 i) (hsNorm_nonneg _) (hcX i)
    simp only [←hs_eq_hsNorm] at ha hb
    have hdiv : (Real.sqrt (bSquared X Z s i)+hs (comm (X i) s.xi))^2/(2*Real.log 2)≤
        (bSquared X Z s i+4*lambda i^2)/Real.log 2 := by
      apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*Real.log 2) hlog).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hb hlog.le]
    have hcap := CountProof.binaryEntropy_mono_half
      (show min ((Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4) (1/2)∈Set.Icc 0 (1/2)
        from ⟨le_min (by positivity) (by norm_num),min_le_right _ _⟩)
      (show min ((aSquared Z s i+4*lambda i^2)/2) (1/2)∈Set.Icc 0 (1/2)
        from ⟨le_min (div_nonneg (add_nonneg (ha0 i) (by positivity)) (by norm_num))
          (by norm_num),min_le_right _ _⟩)
      (min_le_min_right (1/2) (by linarith :
        (Real.sqrt (aSquared Z s i)+hs (comm (Z i) s.xi))^2/4≤(aSquared Z s i+4*lambda i^2)/2))
    linarith
  have hsum := (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hpoint i)).trans
    (CountProof.count_entropy_bound X Z hX hZ s)
  have hj := cappedEntropy_concave.le_map_sum (t:=Finset.univ)
    (w:=fun _ : Fin M => (M:ℝ)⁻¹)
    (p:=fun i => (aSquared Z s i+4*lambda i^2)/2)
    (fun i _ => inv_nonneg.mpr hM0.le)
    (by simp [ne_of_gt hM0]) (fun i _ =>
      div_nonneg (add_nonneg (ha0 i) (by positivity)) (by norm_num))
  simp only [smul_eq_mul,←Finset.mul_sum] at hj
  have hmean : (M:ℝ)⁻¹*(∑ i, (aSquared Z s i+4*lambda i^2)/2)=
      (∑ i, (aSquared Z s i+4*lambda i^2))/(2*M) := by
    rw [←Finset.sum_div]
    ring
  rw [hmean] at hj
  have hj' := mul_le_mul_of_nonneg_left hj hM0.le
  rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hM0),one_mul] at hj'
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,←Finset.sum_div] at hsum
  linarith

theorem binaryEntropy_sixteenth : binaryEntropy (1/16)≤(7/20:ℝ) := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h16 : Real.log 16=4*Real.log 2 := by
    have hh := Real.log_pow 2 4
    norm_num at hh
    exact hh
  have h15 : Real.log ((16:ℝ)/15)≤1/15 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<16/15)
    linarith
  have he : binaryEntropy (1/16)=
      ((1/16)*Real.log 16+(15/16)*Real.log (16/15))/Real.log 2 := by
    norm_num [binaryEntropy,Real.binEntropy]
  rw [he]
  apply (div_le_iff₀ hl).mpr
  rw [h16]
  nlinarith [Real.log_two_gt_d9]

theorem numeric_threshold : (1:ℝ)-1240000*(1/10000000)-binaryEntropy (311000/10000000)≥1/2 := by
  have hh := CountProof.binaryEntropy_mono_half
    (by norm_num : (311000/10000000:ℝ)∈Set.Icc 0 (1/2))
    (by norm_num : (1/16:ℝ)∈Set.Icc 0 (1/2)) (by norm_num)
  linarith [binaryEntropy_sixteenth]

theorem entropy_cutoff (M : Nat) (eps A B H : ℝ) (hM : 1≤M) (he : 0<eps)
    (hME : (M:ℝ)*eps≤1/30000000) (hA0 : 0≤A)
    (hA : A≤73162*(3*(M:ℝ))^2*(2*Real.sqrt 2*eps))
    (hB : B≤101256*(3*(M:ℝ))^2*(2*Real.sqrt 2*eps))
    (hH : (M:ℝ)-B/Real.log 2-M*binaryEntropy (min (A/(2*M)) (1/2))≤H) :
    (M:ℝ)/2≤H := by
  have hM0 : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : Real.sqrt 2≤283/200 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hcoefA : 1316916*Real.sqrt 2/30000000≤(1/8:ℝ) := by nlinarith
  have hcoefB : 1822608*Real.sqrt 2/30000000≤(1/8:ℝ)*Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hAmax : A≤(1/8:ℝ)*M := by
    calc
      _≤73162*(3*(M:ℝ))^2*(2*Real.sqrt 2*eps) := hA
      _=1316916*Real.sqrt 2*(M:ℝ)*((M:ℝ)*eps) := by ring
      _≤1316916*Real.sqrt 2*(M:ℝ)*(1/30000000) :=
        mul_le_mul_of_nonneg_left hME (by positivity)
      _≤(1/8:ℝ)*M := by nlinarith only [mul_le_mul_of_nonneg_right hcoefA hM0.le]
  have hBmax : B≤((M:ℝ)/8)*Real.log 2 := by
    calc
      _≤101256*(3*(M:ℝ))^2*(2*Real.sqrt 2*eps) := hB
      _=1822608*Real.sqrt 2*(M:ℝ)*((M:ℝ)*eps) := by ring
      _≤1822608*Real.sqrt 2*(M:ℝ)*(1/30000000) :=
        mul_le_mul_of_nonneg_left hME (by positivity)
      _≤((M:ℝ)/8)*Real.log 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hcoefB hM0.le]
  have hBdiv : B/Real.log 2≤(M:ℝ)/8 := (div_le_iff₀ hlog).mpr hBmax
  have hAdiv : A/(2*M)≤(1/16:ℝ) :=
    (div_le_iff₀ (by positivity : (0:ℝ)<2*M)).mpr (by linarith)
  have hcap := CountProof.binaryEntropy_mono_half
    (show min (A/(2*M)) (1/2)∈Set.Icc (0:ℝ) (1/2) from
      ⟨le_min (div_nonneg hA0 (by positivity)) (by norm_num),min_le_right _ _⟩)
    (by norm_num : (1/16:ℝ)∈Set.Icc 0 (1/2))
    ((min_le_left _ _).trans hAdiv)
  have hcapM := mul_le_mul_of_nonneg_left (hcap.trans binaryEntropy_sixteenth) hM0.le
  linarith

theorem entropy_lower : ELower := by
  intro n a b psi A B eps hn he hv hb
  let s := W2.aliceState psi hv.1
  have hrho : s.rho=(psi.conjTranspose*psi).transpose := rfl
  have hent : entropy s.rho=entropy (psi.conjTranspose*psi) := alice_entropy psi s hrho
  let M := chshM n eps
  have hFirst : (M:ℝ)/2≤entropy s.rho := by
    by_cases hMzero : M=0
    · simpa only [hMzero,Nat.cast_zero,zero_div] using Companion.Analytic.entropy_nonneg s
    have hM : 1≤M := by omega
    obtain ⟨A',B',hA,hB,hbias⟩ := optimize psi A B hv
    have hw : (1-eps)*optimalBias≤chshBias psi A' B' := hb.trans hbias
    have hdef := deficit_budget (by omega : 2≤n) psi hv.1 A' B' hA hB eps hw
    let delta : Fin n → Fin n → ℝ := fun i j =>
      if i<j then 2*Real.sqrt 2-chshPair psi A' B' i j
      else if j < i then 2*Real.sqrt 2-chshPair psi A' B' j i else 0
    have hd (i j : Fin n) : 0≤delta i j := by
      dsimp [delta]
      split
      · exact hdef.1 i j ‹_›
      · split
        · exact hdef.1 j i ‹_›
        · exact le_rfl
    have hsym (i j : Fin n) : delta i j=delta j i := by
      rcases lt_trichotomy i j with hij | rfl | hji
      · simp [delta,hij,not_lt_of_ge hij.le]
      · rfl
      · simp [delta,hji,not_lt_of_ge hji.le]
    have hdeltaSum : (∑ i, ∑ j, if i<j then delta i j else 0)≤
        2*Real.sqrt 2*eps*(n.choose 2) := by
      convert hdef.2 using 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split <;> simp_all [delta]
    have hfloor : (M:ℝ)≤min (n:ℝ) ((1/10000000:ℝ)/eps)/3 :=
      Nat.floor_le (div_nonneg (le_min (Nat.cast_nonneg _) (by positivity)) (by norm_num))
    have h3M : (3:ℝ)*M≤min (n:ℝ) ((1/10000000:ℝ)/eps) := by linarith
    have hsize : 3*M≤n := by
      have hh := h3M.trans (min_le_left _ _)
      exact_mod_cast hh
    have hME : (M:ℝ)*eps≤1/30000000 := by
      have hh := mul_le_mul_of_nonneg_right (h3M.trans (min_le_right _ _)) he.le
      rw [div_mul_cancel₀ _ (ne_of_gt he)] at hh
      nlinarith only [hh]
    obtain ⟨f,hsel,hint⟩ := subset_triples n M hM hsize delta hd hsym eps hdeltaSum
    have hpair (i j : Fin n) (hij : i<j) :=
      one_pair psi hv.1 (A' i) (A' j) (B' i j) (B' j i)
        (hA i) (hA j) (hB i j (ne_of_lt hij)) (hB j i (ne_of_gt hij)) s hrho
    have hanti (i j : Fin n) (hij : i≠j) :
        hs (anti (A' i) (A' j)*s.xi)^2≤33*delta i j := by
      rcases lt_or_gt_of_ne hij with h | h
      · simpa only [delta,ite_eq_left h,chshPair] using (hpair i j h).2.2.1
      · have ha : anti (A' i) (A' j)=anti (A' j) (A' i) := by unfold anti; abel
        rw [ha]
        simpa only [delta,ite_eq_right (not_lt_of_ge h.le),ite_eq_left h,chshPair] using (hpair j i h).2.2.1
    have hc (i j : Fin n) (hij : i≠j) :
        hs (comm (A' i) s.xi)^2≤2*Real.sqrt 2*delta i j := by
      rcases lt_or_gt_of_ne hij with h | h
      · simpa only [delta,ite_eq_left h,chshPair] using (hpair i j h).2.2.2.1
      · simpa only [delta,ite_eq_right (not_lt_of_ge h.le),ite_eq_left h,chshPair] using (hpair j i h).2.2.2.2
    let T := fun k r => A' (f (k,r))
    let X := fun k => tripleX (T k)
    let Z := fun k => tripleZ (T k)
    let lam := fun k => lambdaTriple (T k) s
    let mu := fun k l => muTriple (T k) (T l) s
    have hT (k : Fin M) (r : Fin 3) : IsInvolution (T k r) := hA _
    have ht (k : Fin M) := triple_bounds (T k) s (hT k)
    have hcross (k l : Fin M) := cross_triple_bounds (T k) (T l) s (hT k) (hT l)
    have hsel' : (∑ x, ∑ y, if f x<f y then delta (f x) (f y) else 0)≤
        ((3*M).choose 2)*(2*Real.sqrt 2*eps) := by nlinarith only [hsel]
    have hint' : (∑ k, ∑ r : Fin 3, ∑ t : Fin 3, if r<t then delta (f (k,r)) (f (k,t)) else 0)≤
        (3*M:Nat)*(2*Real.sqrt 2*eps) := by
      push_cast
      nlinarith only [hint]
    have herrors := selected_error_sums hM A' s f delta (2*Real.sqrt 2*eps)
      hd hsym hanti hc hsel' hint'
    have hlam (k : Fin M) : 0≤lam k := by dsimp [lam,lambdaTriple,hs]; positivity
    have hmu (k l : Fin M) : 0≤mu k l := by dsimp [mu,muTriple,hs]; positivity
    have hcounts := count_error_budget hM X Z s lam mu (2*Real.sqrt 2*eps)
      hlam hmu (fun k => (ht k).1) (fun k => (ht k).2.1)
      (fun k l _ => (hcross k l).1) (fun k l _ => (hcross k l).2)
      (fun k => (ht k).2.2.1) (fun k => (ht k).2.2.2.1) (fun k => (ht k).2.2.2.2)
      herrors.1 herrors.2
    have hcountEntropy := entropy_jensen hM X Z s lam (fun k => (ht k).1)
      (fun k => (ht k).2.1) (fun k => (ht k).2.2.2.1) (fun k => (ht k).2.2.2.2)
    refine entropy_cutoff M eps (∑ k, (aSquared Z s k+4*lam k^2))
      (∑ k, (bSquared X Z s k+4*lam k^2)) _ hM he hME ?_ ?_ ?_ hcountEntropy
    · apply Finset.sum_nonneg
      intro k _
      unfold aSquared
      positivity
    · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcounts.1
    · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcounts.2
  rw [hent] at hFirst
  refine ⟨hFirst,?_⟩
  have ht0 : 0≤min (n:ℝ) (1/eps) := le_min (Nat.cast_nonneg _) (by positivity)
  have hscale : (1/10000000:ℝ)*min (n:ℝ) (1/eps)≤
      min (n:ℝ) ((1/10000000:ℝ)/eps) := by
    apply le_min
    · have hh := min_le_left (n:ℝ) (1/eps)
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left (min_le_right (n:ℝ) (1/eps))
        (by norm_num : (0:ℝ)≤1/10000000)
      convert hh using 1 <;> ring
  have hf := Nat.sub_one_lt_floor (min (n:ℝ) ((1/10000000:ℝ)/eps)/3)
  change min (n:ℝ) ((1/10000000:ℝ)/eps)/3-1<(M:ℝ) at hf
  linarith

theorem jordan_wigner (n : Nat) (hn : 2≤n) : ∃ A : Fin n → Mat (2^(n/2)),
    (∀ i, IsInvolution (A i)) ∧ ∀ i j, i≠j → anti (A i) (A j)=0 := by
  obtain ⟨A,hA,ha⟩ := W2.clifford_family (n/2)
  have hn' : n≤2*(n/2)+1 := by omega
  let f : Fin n ↪ Fin (2*(n/2)+1) := Fin.castLEEmb hn'
  exact ⟨fun i => A (f i),fun i => hA (f i),fun i j hij => ha (f i) (f j) (f.injective.ne hij)⟩

/-- A direct CHSH(n) construction attaining the dimension budget of OV18 Theorem 2.
Balanced modulo labels in a Clifford family suffice for this specialized game. -/
theorem approximate_upper (n : Nat) (eps : ℝ) (hn : 2≤n) (he : 0<eps) :
    ∃ a b psi A B, validCHSH (n:=n) (a:=a) (b:=b) psi A B ∧
      (1-eps)*optimalBias≤chshBias psi A B ∧ entropy (psi.conjTranspose*psi)≤(⌈1/eps⌉₊:ℝ) := by
  let m := ⌈1/eps⌉₊
  obtain ⟨G,hG,ha⟩ := W2.clifford_family m
  have hd : 0<2^m := by positivity
  have hk : 0<2*m+1 := by omega
  let f : Fin n → Fin (2*m+1) := fun i => ⟨i.val%(2*m+1),Nat.mod_lt _ hk⟩
  let A := fun i => G (f i)
  let B := W2.collisionBob G f
  let s := MainProof.flatState (2^m) hd
  have hanti : ∀ i j, i≠j → anti (G i) (G j)=0 := ha
  refine ⟨2^m,2^m,s.xi,A,B,⟨ReturnProof.state_xi_normalized s,
    fun i => W2.involution_contraction hd _ (hG _),fun i j _ =>
      W2.involution_contraction hd _ (W2.collisionBob_involution G f hG hanti i j)⟩,?_,?_⟩
  · exact W2.collision_bias hn hk hd G hG eps (W2.ceiling_collision_budget n hn eps he)
  · have h := W2.flat_entropy hd
    have hlog : Real.log ((2^m:Nat):ℝ)/Real.log 2=m := by
      rw [Nat.cast_pow,Real.log_pow]
      field_simp
      norm_num
    simpa only [s,hlog] using h

theorem exact_upper (n : Nat) (hn : 2≤n) : ∃ psi A B,
    validCHSH (n:=n) (a:=2^(n/2)) (b:=2^(n/2)) psi A B ∧
      chshBias psi A B=optimalBias ∧ entropy (psi.conjTranspose*psi)≤((n/2:Nat):ℝ) := by
  obtain ⟨A,hA,ha⟩ := jordan_wigner n hn
  have hd : 0<2^(n/2) := by positivity
  let s := MainProof.flatState (2^(n/2)) hd
  let B := W2.exactBob A
  refine ⟨s.xi,A,B,⟨ReturnProof.state_xi_normalized s,
    fun i => W2.involution_contraction hd _ (hA i),
    fun i j _ => W2.involution_contraction hd _ (W2.exactBob_involution A hA ha i j)⟩,?_,?_⟩
  · have hp (i j : Fin n) (hij : i<j) : chshPair s.xi A B i j=2*Real.sqrt 2 := by
      obtain ⟨hplus,hminus⟩ := W2.exactBob_pair A i j hij
      dsimp [chshPair,B]
      rw [hplus,hminus,W2.flat_expectation hd (A i) (hA i),W2.flat_expectation hd (A j) (hA j)]
      ring
    unfold chshBias
    have hsum : (∑ i : Fin n, ∑ j : Fin n, if i<j then chshPair s.xi A B i j else 0)=
        (2*Real.sqrt 2)*(n.choose 2) := by
      calc
        _=∑ i : Fin n, ∑ j : Fin n, (2*Real.sqrt 2)*(if i<j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          split <;> simp_all [hp]
        _=_ := by simp_rw [←Finset.mul_sum]; rw [W2.pair_count]
    rw [hsum,W2.choose_two_cast]
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
    have hn1 : ((n-1:Nat):ℝ)≠0 := by exact_mod_cast (by omega : n-1≠0)
    unfold optimalBias
    field_simp
    <;> ring
  · have h := W2.flat_entropy hd
    have hlog : Real.log ((2^(n/2):Nat):ℝ)/Real.log 2=(n/2:Nat) := by
      rw [Nat.cast_pow,Real.log_pow]
      field_simp
      norm_num
    simpa only [s,hlog] using h

theorem profiles : EProfiles := by
  intro n eps hn he hsmall
  let S : Set ℝ := {v | ∃ a b psi A B, validCHSH (n:=n) (a:=a) (b:=b) psi A B ∧
    (1-eps)*optimalBias≤chshBias psi A B ∧ v=entropy (psi.conjTranspose*psi)}
  have hlower : ∀ v∈S, (1/60000000:ℝ)*min (n:ℝ) (1/eps)-1/2≤v := by
    rintro v ⟨a,b,psi,A,B,hv,hw,rfl⟩
    exact (entropy_lower n a b psi A B eps hn he hv hw).2
  have hbounded : BddBelow S := ⟨_,hlower⟩
  obtain ⟨psi,A,B,hv,hw,hent⟩ := exact_upper n (by omega)
  have hw' : (1-eps)*optimalBias≤chshBias psi A B := by
    rw [hw]
    have hp : 0≤optimalBias := by unfold optimalBias; positivity
    nlinarith
  have hexact : entropy (psi.conjTranspose*psi)∈S :=
    ⟨2^(n/2),2^(n/2),psi,A,B,hv,hw',rfl⟩
  obtain ⟨a,b,psi',A',B',hv',hw'',hent'⟩ := approximate_upper n eps (by omega) he
  have happrox : entropy (psi'.conjTranspose*psi')∈S := ⟨a,b,psi',A',B',hv',hw'',rfl⟩
  change _≤sInf S ∧ sInf S≤_
  exact ⟨le_csInf ⟨_,hexact⟩ hlower,
    le_min ((csInf_le hbounded hexact).trans hent) ((csInf_le hbounded happrox).trans hent')⟩
theorem mixed_lower : EMixed := MixedStates.chsh_from_pure entropy_lower

end
end Blueprint.ERates
