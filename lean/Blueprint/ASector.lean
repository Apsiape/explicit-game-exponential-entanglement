import Blueprint.A.SectorState
import Blueprint.A.PairFromLocal
import Blueprint.A.SectorAssembly
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Companion.UniformCountTheorem
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace Blueprint.ASector
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

/-- Pair-area input, including the quantitative Dehn bound used by the paper. -/
theorem pair_areas
    (N : Nat) (hN : 1≤N) : ∃ (T : (Fin N → Bool) → Word) (L : Nat),
    (∀ u, (T u).length≤21*N*max 3 N) ∧
    14000*N^2*max 3 N≤L ∧ (L:ℝ)≤(2:ℝ)^((log2 N+23)^2) ∧
    (∀ u v, u≠v → ∀ a∈[5,6], ∀ b∈[5,6],
      FiniteArea.Area sourceRelator (FreeGroup.mk (commWord (transportLamp (T u) a) (transportLamp (T v) b))) L) ∧
    (∀ u, FiniteArea.Area sourceRelator
      (FreeGroup.mk (T u++lampJ++FreeGroup.invRev (T u)++FreeGroup.invRev lampJ)) (4*(T u).length)) :=
  PairProof.pair_areas_from_local N hN

theorem sector_pauli
    (hconj : Published.ConjugatorLengths)
    {d : Nat} (U : Nat → Mat d) (s : State d) (e delta : ℝ)
    (he : 0<e) (hd : 0<delta) (hd2 : delta≤2) (hm : sourceModel U s e)
    (hv : delta≤hs ((wordEval U lampJ-1)*s.xi)) (N : Nat) (hN : 1≤N)
    (hscale : (2:ℝ)^N*((2:ℝ)^((log2 N+23)^2))^4≤delta^2/(10200000*e^2)) :
    ∃ (t : State d) (X Z : Fin (2^N) → Mat d) (kappa : ℝ),
      (∀ i, IsInvolution (X i)) ∧ (∀ i, IsInvolution (Z i)) ∧
      (∀ i j, i≠j → hs (comm (Z i) (Z j)*t.xi)≤kappa) ∧
      (∀ i j, i≠j → hs (comm (X i) (Z j)*t.xi)≤kappa) ∧
      (∀ i, hs (anti (X i) (Z i)*t.xi)≤kappa) ∧
      (∀ i, hs (comm (X i) t.xi)≤kappa) ∧ (∀ i, hs (comm (Z i) t.xi)≤kappa) ∧
      16*((2^N:Nat):ℝ)*kappa^2≤1/10 ∧ entropy t.rho*delta^2/16-1≤entropy s.rho ∧
      rank t.rho≤rank s.rho :=
  ASectorProof.sector_pauli_proof hconj U s e delta he hd hd2 hm hv N hN hscale

def scaleGrowth (N : Nat) : ℝ := N+4*(log2 N+23)^2

theorem scale_index (Q : ℝ) (hQ : 2117≤Q) : ∃ N : Nat, 1≤N ∧
    scaleGrowth N≤Q ∧ Q<scaleGrowth (N+1) := by
  classical
  have hex : ∃ m : Nat, Q<scaleGrowth m := by
    obtain ⟨m,hm⟩ := exists_nat_gt Q
    exact ⟨m,hm.trans_le (by unfold scaleGrowth; nlinarith [sq_nonneg (log2 m+23)])⟩
  let k := Nat.find hex
  have hk : Q<scaleGrowth k := Nat.find_spec hex
  have hk2 : 2≤k := by
    by_contra hh
    have hh' : k=0 ∨ k=1 := by omega
    rcases hh' with hh'|hh' <;> rw [hh'] at hk <;> norm_num [scaleGrowth,log2] at hk <;> linarith
  refine ⟨k-1,by omega,?_,?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by change k-1<k; omega))
  · simpa only [Nat.sub_add_cancel (by omega : 1≤k)] using hk

theorem scale_choice (e delta : ℝ) (he : 0<e) (hd : 0<delta) (hd2 : delta≤2)
    (hsmall : e≤(2:ℝ)^(-1071:ℤ)*delta) : ∃ N : Nat, 1≤N ∧
    (2:ℝ)^N*((2:ℝ)^((log2 N+23)^2))^4≤delta^2/(10200000*e^2) ∧
    sourceC*delta^2/e^2*bfun e≤(3/4:ℝ)*(2:ℝ)^N := by
  let R : ℝ := delta^2/(10200000*e^2)
  let Q : ℝ := log2 R
  let t : ℝ := log2 (1/e)
  have hL : 0<Real.log 2 := Real.log_pos (by norm_num)
  have he2 : 0<e^2 := sq_pos_of_pos he
  have hdSq : 0<delta^2 := sq_pos_of_pos hd
  have hR : 0<R := div_pos hdSq (mul_pos (by norm_num) he2)
  have hsq : e^2≤((2:ℝ)^(-1071:ℤ))^2*delta^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ he.le (by positivity)).mpr hsmall
  have hbase : (2:ℝ)^2117≤R := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<10200000) he2)).mpr
    have hc : (2:ℝ)^2117*10200000*((2:ℝ)^(-1071:ℤ))^2≤1 := by
      set_option exponentiation.threshold 3000 in norm_num
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ)≤(2:ℝ)^2117*10200000)
    have hh' := mul_le_mul_of_nonneg_right hc hdSq.le
    calc
      _=(2:ℝ)^2117*10200000*e^2 := by ring
      _≤(2:ℝ)^2117*10200000*(((2:ℝ)^(-1071:ℤ))^2*delta^2) := hh
      _=((2:ℝ)^2117*10200000*((2:ℝ)^(-1071:ℤ))^2)*delta^2 := by ring
      _≤delta^2 := by simpa only [one_mul] using hh'
  have hQ : (2117:ℝ)≤Q := by
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^2117) hbase
    rw [Real.log_pow] at hh
    exact (le_div_iff₀ hL).mpr (by simpa using hh)
  have hRlt : R<(1/e)^2 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<10200000) he2)).mpr
    have hd4 : delta^2≤4 := by nlinarith
    have hh : (1/e)^2*(10200000*e^2)=(10200000:ℝ) := by field_simp
    rw [hh]
    linarith
  have hQt : Q<2*t := by
    have hh := Real.log_lt_log hR hRlt
    rw [Real.log_pow] at hh
    dsimp [Q,t,log2]
    apply (div_lt_iff₀ hL).mpr
    convert hh using 1 <;> field_simp <;> ring
  obtain ⟨N,hN,hG,hNext⟩ := scale_index Q hQ
  have hlogN : 0≤log2 N := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hN)) hL.le
  have hNQ : (N:ℝ)+1≤Q := by
    dsimp [scaleGrowth] at hG
    nlinarith [sq_nonneg (log2 N)]
  have hnp : (0:ℝ)<N+1 := by positivity
  have ht : 0<t := by linarith
  have hlogNext : log2 ((N:ℝ)+1)≤1+log2 t := by
    have hh := Real.log_le_log hnp (by linarith : (N:ℝ)+1≤2*t)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) ht.ne'] at hh
    dsimp [log2]
    apply (div_le_iff₀ hL).mpr
    convert hh using 1 <;> field_simp <;> ring
  have hlnonneg : 0≤log2 ((N:ℝ)+1) := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (by omega : 1≤N+1))) hL.le
  have hB : (log2 ((N:ℝ)+1)+23)^2≤(24+log2 t)^2 :=
    (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)
  have hExp : Q-1-4*(24+log2 t)^2<(N:ℝ) := by
    simp only [scaleGrowth,Nat.cast_add,Nat.cast_one] at hNext
    linarith
  have hPowQ : (2:ℝ)^Q=R := by
    exact Real.rpow_logb (by norm_num) (by norm_num) hR
  have hNear : R*bfun e/2<(2:ℝ)^N := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hExp
    rw [Real.rpow_natCast] at hh
    convert hh using 1
    rw [sub_eq_add_neg,sub_eq_add_neg,Real.rpow_add (by norm_num),
      Real.rpow_add (by norm_num),hPowQ]
    norm_num
    unfold bfun
    dsimp [t]
    simp only [neg_mul]
    ring
  have hScale : (2:ℝ)^N*((2:ℝ)^((log2 N+23)^2))^4≤R := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hG
    rw [hPowQ] at hh
    convert hh using 1
    rw [scaleGrowth,Real.rpow_add (by norm_num),Real.rpow_natCast]
    congr 1
    rw [←Real.rpow_natCast _ 4,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  refine ⟨N,hN,hScale,?_⟩
  have hb : 0<bfun e := Real.rpow_pos_of_pos (by norm_num) _
  have heq : sourceC*delta^2/e^2*bfun e=(10200000*sourceC)*(R*bfun e) := by
    dsimp [R]
    ring
  rw [heq]
  have hc : (0:ℝ)≤10200000*sourceC ∧ (10200000*sourceC)*2≤3/4 := by
    norm_num [sourceC]
  calc
    _≤(10200000*sourceC)*(2*(2:ℝ)^N) := mul_le_mul_of_nonneg_left (by linarith) hc.1
    _≤_ := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) N]


theorem source_sector
    (hconj : Published.ConjugatorLengths)
    {d : Nat} (U : Nat → Mat d) (s : State d) (e delta : ℝ)
    (he : 0<e) (hd : 0<delta) (hd2 : delta≤2) (hm : sourceModel U s e)
    (hv : delta≤hs ((wordEval U lampJ-1)*s.xi)) (hsmall : e≤(2:ℝ)^(-1071:ℤ)*delta) :
    sourceC/16*delta^4/e^2*bfun e-1≤entropy s.rho ∧
      sourceC*delta^2/e^2*bfun e≤log2 (rank s.rho:ℝ) := by
  obtain ⟨N,hN,hscale,hchoice⟩ := scale_choice e delta he hd hd2 hsmall
  obtain ⟨t,X,Z,k,hX,hZ,hZZ,hXZ,ha,hcX,hcZ,hk,hent,hrank⟩ :=
    sector_pauli hconj U s e delta he hd hd2 hm hv N hN hscale
  have hM : 2≤2^N := by
    calc
      2=2^1 := by norm_num
      _≤2^N := Nat.pow_le_pow_right (by decide) hN
  have hcount := CountProof.uniformCount (2^N) d X Z t k hM hX hZ hZZ hXZ ha hcX hcZ hk
  have hchoice' : sourceC*delta^2/e^2*bfun e≤entropy t.rho := by
    have hnat : sourceC*delta^2/e^2*bfun e≤(3/4:ℝ)*((2^N:Nat):ℝ) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hchoice
    exact hnat.trans hcount.1
  constructor
  · calc
      sourceC/16*delta^4/e^2*bfun e-1=
          (sourceC*delta^2/e^2*bfun e)*(delta^2/16)-1 := by ring
      _≤entropy t.rho*(delta^2/16)-1 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_right hchoice' (by positivity)) 1
      _≤entropy s.rho := by convert hent using 1 <;> ring
  · have hp : (0:ℝ)<rank t.rho := by exact_mod_cast CountProof.state_rank_pos t
    have hr : (rank t.rho:ℝ)≤rank s.rho := by exact_mod_cast hrank
    have hlog : log2 (rank t.rho:ℝ)≤log2 (rank s.rho:ℝ) :=
      div_le_div_of_nonneg_right (Real.log_le_log hp hr) (Real.log_pos (by norm_num)).le
    exact hchoice'.trans ((CountProof.entropy_le_log_rank t).trans hlog)

end
end Blueprint.ASector

-- ROUND-12 DECLARATION AUDIT
#print axioms Blueprint.ASector.commWord
#print axioms Blueprint.ASector.transportLamp
#print axioms Blueprint.ASector.sourceRelator
#print axioms Blueprint.ASector.area_one
#print axioms Blueprint.ASector.area_weaken
#print axioms Blueprint.ASector.area_mul
#print axioms Blueprint.ASector.area_inv
#print axioms Blueprint.ASector.area_conj
#print axioms Blueprint.ASector.groupComm
#print axioms Blueprint.ASector.area_comm_mul
#print axioms Blueprint.ASector.area_comm_inv
#print axioms Blueprint.ASector.centralFactors
#print axioms Blueprint.ASector.central_factors_checked
#print axioms Blueprint.ASector.lampJ_letter_area
#print axioms Blueprint.ASector.lampJ_transport_area
#print axioms Blueprint.ASector.sqrt_residual_bound
#print axioms Blueprint.ASector.pair_areas
#print axioms Blueprint.ASector.sector_state
#print axioms Blueprint.ASector.sector_pauli
#print axioms Blueprint.ASector.scaleGrowth
#print axioms Blueprint.ASector.scale_index
#print axioms Blueprint.ASector.scale_choice
#print axioms Blueprint.ASector.source_sector
#print axioms CFC.sqrt_le_sqrt
