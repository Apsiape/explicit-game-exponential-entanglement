import Blueprint.A.PairFromLocal
import Blueprint.A.LampMarker
import Blueprint.A.SectorConditioning
import Blueprint.A.SectorEntropy
import Blueprint.A.SectorNumerics

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic ASector PairProof Published
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem sector_pauli_proof
    (hconj : ConjugatorLengths)
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
      rank t.rho≤rank s.rho := by
  classical
  obtain ⟨T,L,hT,hL,hLtop,hpair,hTJ,hletters⟩ := pair_areas_supported N hN
  let ell := 21*N*max 3 N
  obtain ⟨hell,h100,hlarge⟩ := sector_length_constants N L hN hL
  let index : Fin (2^N) ≃ (Fin N → Bool) := Fintype.equivOfCardEq (by simp)
  let Ti : Fin (2^N) → Word := fun i => T (index i)
  let R : Nat → Fin (2^N) → Mat d := fun a i => roundUnitary (wordEval U (transportLamp (Ti i) a))
  let W := wordEval U lampJ
  let J := roundUnitary W
  let p := (signProjection J true*s.rho).trace.re
  let kappa := 252*(L:ℝ)^2*e/delta
  have hlen : ∀ i, (Ti i).length≤ell := fun i => hT (index i)
  have hTi : ∀ i, ∀ a∈Ti i, 1≤a.1 ∧ a.1≤6 := by
    intro i a ha
    have hh := hletters (index i) a ha
    omega
  have hround : ∀ i a, a∈[5,6] → IsInvolution (R a i) ∧
      hs ((R a i-wordEval U (transportLamp (Ti i) a))*s.xi)≤(2*ell+1)*e ∧
      hs (comm (R a i) s.xi)≤7*ell*e := by
    intro i a ha
    exact transported_lamp_rounding U s e he.le hm (Ti i) (hTi i) a ha ell (hlen i) (by omega)
  obtain ⟨hJ,hJW,hJC⟩ := lampJ_rounding U s e hm
  change IsInvolution J at hJ
  change hs ((J-W)*s.xi)≤e at hJW
  change hs (comm J s.xi)≤6*e at hJC
  have hsmall := scale_error_small N e delta he hd hscale
  have hvis : delta/2≤hs ((J-1)*s.xi) := by
    have hh := CountProof.hs_sub_le ((J-1)*s.xi) ((J-W)*s.xi)
    have heq : (J-1)*s.xi-(J-W)*s.xi=(W-1)*s.xi := by
      simp only [Matrix.sub_mul]; abel
    rw [heq] at hh
    change delta≤hs ((W-1)*s.xi) at hv
    simp only [hs_eq_hsNorm] at hh hv hJW ⊢
    linarith
  have hp : delta^2/16≤p := by
    have hh := SV.sector_probability s J hJ
    have hSq : (delta/2)^2≤hs ((J-1)*s.xi)^2 :=
      (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mpr hvis
    change hs ((J-1)*s.xi)^2=4*p at hh
    nlinarith
  have hp0 : 0<p := lt_of_lt_of_le (by positivity : (0:ℝ)<delta^2/16) hp
  obtain ⟨t,htrho,ht0⟩ := sector_state s J hJ hp0
  have ht : hs (t.xi-((Real.sqrt p)⁻¹:ℂ) •
      (signProjection J true*s.xi*signProjection J true))≤hs (comm J s.xi)/(2*Real.sqrt p) := by
    apply ht0.trans
    have hh := div_le_div_of_nonneg_right (SV.off_diagonal_hs J s.xi hJ) (Real.sqrt_nonneg p)
    convert hh using 1 <;> ring
  have hdim : 0<d := by
    have hh := Fintype.card_pos_iff.mpr s.toQuAIR.nonempty
    simpa only [Fintype.card_fin] using hh
  have hnums := sector_numerators ell L hell h100 hlarge e he.le
  have hdiv := sector_division_bound L e delta p he.le hd hp
  have hq : 0≤Real.sqrt p := Real.sqrt_nonneg p
  have hG : ∀ i, hs ((R 5 i*R 6 i*R 5 i*R 6 i-J)*s.xi)≤10000*(ell:ℝ)^2*e := by
    intro i
    exact lamp_marker_bound hconj U s e he.le hm (Ti i) (hTi i) ell hell (hlen i)
      (hTJ (index i)) (R 5 i) (R 6 i)
      (CountProof.involution_unitary _ (hround i 5 (by simp)).1)
      (CountProof.involution_unitary _ (hround i 6 (by simp)).1)
      (hround i 5 (by simp)).2.1 (hround i 6 (by simp)).2.1
  have hstate := fun i => pauli_sector_bounds hdim s t J (R 5 i) (R 6 i) hJ
    (hround i 5 (by simp)).1 (hround i 6 (by simp)).1 hp0 ht
    (10000*(ell:ℝ)^2*e) (7*ell*e) (6*e) (hG i)
    (hround i 5 (by simp)).2.2 (hround i 6 (by simp)).2.2 hJC
  have hcross : ∀ i j, i≠j → ∀ a∈[5,6], ∀ b∈[5,6], hs (comm (R a i) (R b j)*t.xi)≤kappa := by
    intro i j hij a ha b hb
    have hword (i : Fin (2^N)) (a : Nat) (ha : a∈[5,6]) :
        ∀ x∈transportLamp (Ti i) a, 1≤x.1 ∧ x.1≤6 :=
      transport_letters (Ti i) a (fun k => 1≤k ∧ k≤6) (hTi i)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ha; omega)
    have hlength (i : Fin (2^N)) (a : Nat) : (transportLamp (Ti i) a).length≤2*ell+1 := by
      have hh := hlen i
      simp only [transportLamp,List.length_append,List.length_cons,List.length_nil,FreeGroup.invRev_length]
      omega
    have hRa := CountProof.involution_unitary _ (hround i a ha).1
    have hRb := CountProof.involution_unitary _ (hround j b hb).1
    have hbase := cross_bound_from_area hconj U s e he.le hm _ _ (hword i a ha) (hword j b hb)
      ell L (by omega) (hlength i a) (hlength j b) h100
      (hpair (index i) (index j) (fun hh => hij (index.injective hh)) a ha b hb)
      (R a i) (R b j) hRa hRb (hround i a ha).2.1 (hround j b hb).2.1
    have hh := cross_sector_bound hdim s t J (R a i) (R b j) hJ hRa hRb hp0 ht
      (61*(L:ℝ)^2*e+26*ell*e) (6*e) hbase hJC
    apply hh.trans
    apply le_trans _ hdiv
    apply div_le_div_of_nonneg_right _ hq
    convert hnums.1 using 1 <;> ring
  have hsc : ∀ i, hs (comm (R 5 i) t.xi)≤kappa ∧ hs (comm (R 6 i) t.xi)≤kappa ∧
      hs (anti (R 5 i) (R 6 i)*t.xi)≤kappa := by
    intro i
    obtain ⟨hX,hZ,ha⟩ := hstate i
    have hC : (2*(10000*(ell:ℝ)^2*e)+6*(7*ell*e)+3*(6*e))/Real.sqrt p≤kappa := by
      apply le_trans _ hdiv
      apply div_le_div_of_nonneg_right _ hq
      convert hnums.2.1 using 1 <;> ring
    have hA : (9*(10000*(ell:ℝ)^2*e)+24*(7*ell*e)+15*(6*e))/Real.sqrt p≤kappa := by
      apply le_trans _ hdiv
      apply div_le_div_of_nonneg_right _ hq
      convert hnums.2.2 using 1 <;> ring
    exact ⟨hX.trans hC,hZ.trans hC,ha.trans hA⟩
  have hent := sector_entropy_bound s t J hJ hp0 htrho delta hp
  exact ⟨t,R 5,R 6,kappa,(fun i => (hround i 5 (by simp)).1),(fun i => (hround i 6 (by simp)).1),
    (fun i j hij => hcross i j hij 6 (by simp) 6 (by simp)),
    (fun i j hij => hcross i j hij 5 (by simp) 6 (by simp)),
    (fun i => (hsc i).2.2),(fun i => (hsc i).1),(fun i => (hsc i).2.1),
    sector_precision N L e delta he hd hLtop hscale,hent.1,hent.2⟩

end
end Blueprint.ASectorProof

#print axioms Blueprint.ASectorProof.sector_pauli_proof
