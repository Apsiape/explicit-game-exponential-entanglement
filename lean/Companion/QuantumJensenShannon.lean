import Companion.CoherentPairChannel
import Companion.RelativeEntropyTools

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 600000

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem real_overlap_jensen (L B : Matrix a b ℂ) (p : ℝ) (hp0 : 0<p) (hp1 : p<1)
    (hL : hsNorm L=1) (hB : hsNorm B=1)
    (hc : Matrix.trace (L.conjTranspose*B)=((2*p-1:ℝ):ℂ)) :
    (factorState L hL).relativeEntropy (midpointState (factorState L hL) (factorState B hB))≤
      (binaryEntropy p:EReal) := by
  let Phi := pairChannel L B p hp0 hp1 hL hB hc
  have h0 : Phi.applyState (binaryPure p hp0.le hp1.le false).state=factorState L hL := by
    apply QIT.State.ext
    change QIT.MatrixMap.ofKraus (pairKraus L B p) (binaryPure p hp0.le hp1.le false).state.matrix=_
    exact pairKraus_image L B p hp0 hp1 false
  have h1 : Phi.applyState (binaryPure p hp0.le hp1.le true).state=factorState B hB := by
    apply QIT.State.ext
    change QIT.MatrixMap.ofKraus (pairKraus L B p) (binaryPure p hp0.le hp1.le true).state.matrix=_
    exact pairKraus_image L B p hp0 hp1 true
  have hm : Phi.applyState (binaryDiagonal p hp0.le hp1.le)=
      midpointState (factorState L hL) (factorState B hB) := by
    apply QIT.State.ext
    change Phi.map (binaryDiagonal p hp0.le hp1.le).matrix=(1/2:ℂ) • (L*L.conjTranspose+B*B.conjTranspose)
    rw [← binary_midpoint,map_smul,map_add]
    have ha := congrArg QIT.State.matrix h0
    have hb := congrArg QIT.State.matrix h1
    change Phi.map (binaryPure p hp0.le hp1.le false).state.matrix=L*L.conjTranspose at ha
    change Phi.map (binaryPure p hp0.le hp1.le true).state.matrix=B*B.conjTranspose at hb
    rw [ha,hb]
  have h := QIT.State.relativeEntropy_dataProcessing_channel_ge
    (binaryPure p hp0.le hp1.le false).state (binaryDiagonal p hp0.le hp1.le) Phi
  rw [binary_relativeEntropy p hp0 hp1 false,h0,hm] at h
  exact h

theorem binaryEntropy_mono_half {x y : ℝ} (hx : x ∈ Set.Icc 0 (1/2))
    (hy : y ∈ Set.Icc 0 (1/2)) (hxy : x≤y) : binaryEntropy x≤binaryEntropy y := by
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))
  exact Real.binEntropy_strictMonoOn.monotoneOn (by simpa only [one_div] using hx)
    (by simpa only [one_div] using hy) hxy

theorem binaryEntropy_nonneg_unit {x : ℝ} (hx : x ∈ Set.Icc 0 1) : 0≤binaryEntropy x :=
  div_nonneg (Real.binEntropy_nonneg hx.1 hx.2) (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))

theorem quantum_jensen_shannon (L L' : Matrix a b ℂ) (hL : hsNorm L=1) (hL' : hsNorm L'=1) :
    (factorState L hL).relativeEntropy (midpointState (factorState L hL) (factorState L' hL'))≤
      (binaryEntropy (min (hsNorm (L-L')^2/4) (1/2)):EReal) := by
  let z := Matrix.trace (L.conjTranspose*L')
  let r := ‖z‖
  let B := alignmentPhase z • L'
  have hr0 : 0≤r := norm_nonneg z
  have hr1 : r≤1 := by simpa [r,z,hL,hL'] using factor_overlap_bound L L'
  have hB : hsNorm B=1 := by simp [B,factor_hs_smul,alignmentPhase_norm,hL']
  have hc : Matrix.trace (L.conjTranspose*B)=(r:ℂ) := aligned_overlap L L'
  have hsigma : factorState B hB=factorState L' hL' := by
    apply QIT.State.ext
    exact aligned_factor_product L L'
  have hx0 : 0≤min (hsNorm (L-L')^2/4) (1/2) := le_min (by positivity) (by norm_num)
  have hxh : min (hsNorm (L-L')^2/4) (1/2)≤1/2 := min_le_right _ _
  by_cases hre : r=1
  · have hd := factor_distance_sq L B
    rw [hL,hB,hc,hre,Complex.ofReal_one,Complex.one_re] at hd
    have hn : hsNorm (L-B)=0 := by nlinarith [hsNorm_nonneg (L-B)]
    have he : L=B := sub_eq_zero.mp (norm_eq_zero.mp (by rwa [← hsNorm_eq_frobenius]))
    have hs : factorState L hL=factorState L' hL' := by
      apply QIT.State.ext
      change L*L.conjTranspose=L'*L'.conjTranspose
      rw [he]
      exact aligned_factor_product L L'
    rw [← hs,midpoint_self,relativeEntropy_self]
    exact_mod_cast binaryEntropy_nonneg_unit ⟨hx0,by linarith⟩
  · let p := (1+r)/2
    have hp0 : 0<p := by dsimp [p]; linarith
    have hp1 : p<1 := by dsimp [p]; exact (by linarith [lt_of_le_of_ne hr1 hre])
    have hcp : Matrix.trace (L.conjTranspose*B)=((2*p-1:ℝ):ℂ) := by
      rw [hc]
      congr 1
      dsimp [p]
      ring
    have h := real_overlap_jensen L B p hp0 hp1 hL hB hcp
    rw [hsigma] at h
    have hsym : binaryEntropy p=binaryEntropy (1-p) := by
      simp only [binaryEntropy,Real.binEntropy_one_sub]
    rw [hsym] at h
    have hq0 : 0≤1-p := by linarith
    have hqh : 1-p≤1/2 := by dsimp [p]; linarith
    have hqraw : 1-p≤hsNorm (L-L')^2/4 := by
      have hd := factor_distance_sq L L'
      rw [hL,hL'] at hd
      have hz := Complex.re_le_norm z
      change z.re≤r at hz
      dsimp [p]
      change hsNorm (L-L')^2=1^2-2*z.re+1^2 at hd
      nlinarith
    have hmono := binaryEntropy_mono_half ⟨hq0,hqh⟩ ⟨hx0,hxh⟩ (le_min hqraw hqh)
    exact h.trans (by exact_mod_cast hmono)

theorem quantum_jensen_shannon_of_distance_le (L L' : Matrix a b ℂ)
    (hL : hsNorm L=1) (hL' : hsNorm L'=1) (e : ℝ) (he0 : 0≤e) (he : hsNorm (L-L')≤e) :
    (factorState L hL).relativeEntropy (midpointState (factorState L hL) (factorState L' hL'))≤
      (binaryEntropy (min (e^2/4) (1/2)):EReal) := by
  have hsq := (sq_le_sq₀ (hsNorm_nonneg _) he0).mpr he
  have hmono := binaryEntropy_mono_half
    (show min (hsNorm (L-L')^2/4) (1/2) ∈ Set.Icc 0 (1/2) from
      ⟨le_min (by positivity) (by norm_num),min_le_right _ _⟩)
    (show min (e^2/4) (1/2) ∈ Set.Icc 0 (1/2) from
      ⟨le_min (by positivity) (by norm_num),min_le_right _ _⟩)
    (min_le_min_right _ (by linarith))
  exact (quantum_jensen_shannon L L' hL hL').trans (by exact_mod_cast hmono)

end
end Companion.Analytic.CountProof
