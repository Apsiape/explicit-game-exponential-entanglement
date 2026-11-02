import Companion.TransferAssignment

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

variable {g : LCS} {dA r : Nat}
variable (s : Strategy g dA r) (B : Fin g.system.n → Mat r)
  (P : Fin g.system.equations.length → QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin dA)) (eps : ℝ)
  (hB : ∀ j, IsInvolution (B j))
  (hBob : ∀ j b, s.bob j b=CountProof.symmetryProjection (B j) b)
  (hAlice : ∀ i a, s.alice i a=(P i).effects a)
  (heps : 0≤eps) (hw : 1-eps≤win s)
include hB hBob hAlice heps hw

theorem prepared_generator_consistency (i : Fin g.system.equations.length) (j : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars) :
    hsNorm (usedBob B j*s.psi-s.psi*(outcomeObservable (P i) j).transpose)≤theta g eps := by
  rw [usedBob_in_row B i j hj]
  exact projective_consistency_bound s eps heps hw i j hj (P i) (hAlice i) (B j) (hB j) (hBob j)

theorem prepared_state_commutator (hpd : (s.psi*s.psi.conjTranspose).PosDef) (j : Fin g.system.n) :
    hsNorm (comm (usedBob B j) (QIT.psdSqrt (s.psi*s.psi.conjTranspose)))≤Real.sqrt 2*theta g eps := by
  classical
  by_cases hj : variableAppears g j
  · obtain ⟨i,hi⟩ := hj
    rw [usedBob_in_row B i j hi]
    exact projective_state_commutator s hpd eps heps hw i j hi (P i) (hAlice i) (B j) (hB j) (hBob j)
  · simp only [usedBob,hj,↓reduceIte,comm,Matrix.one_mul,Matrix.mul_one,sub_self]
    have hn := mul_nonneg (Real.sqrt_nonneg 2) (theta_nonneg g eps)
    simpa only [hsNorm,hsSquared,Matrix.zero_apply,Complex.normSq_zero,Finset.sum_const_zero,Real.sqrt_zero] using hn

theorem prepared_commutator_relation (i : Fin g.system.equations.length) (j k : Fin g.system.n)
    (hj : j.val ∈ (g.system.equations[i.val]).vars) (hk : k.val ∈ (g.system.equations[i.val]).vars) :
    hsNorm ((usedBob B j*usedBob B k*usedBob B j*usedBob B k-1)*s.psi)≤transferPrecision g eps := by
  have h1 := prepared_generator_consistency s B P eps hB hBob hAlice heps hw i j hj
  have h2 := prepared_generator_consistency s B P eps hB hBob hAlice heps hw i k hk
  rw [outcomeObservable_transpose] at h1 h2
  have h := commutator_relation_bound s.psi (usedBob B j) (usedBob B k)
    (outcomeObservable (transposePVM (P i)) j) (outcomeObservable (transposePVM (P i)) k)
    (CountProof.involution_unitary _ (usedBob_involution B hB j))
    (CountProof.involution_unitary _ (usedBob_involution B hB k))
    (outcomeObservable_involution _ j) (outcomeObservable_involution _ k)
    (outcomeObservable_commute _ j k) (theta g eps) h1 h2
  exact h.trans (commutator_transfer_constant g eps)

theorem prepared_equation_relation (i : Fin g.system.equations.length) :
    hsNorm ((boolPhase (g.system.equations[i.val]).rhs •
      ((g.system.equations[i.val]).vars.map (naturalBob (usedBob B))).prod-1)*s.psi)≤transferPrecision g eps := by
  let vars := (g.system.equations[i.val]).vars
  let G := usedBob B
  let L := vars.map (fun j => (naturalBob G j,indexedAliceObservable (transposePVM (P i)) j))
  have hL : ∀ p ∈ L, IsUnitary p.1 ∧ IsUnitary p.2 := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hjB : j<g.system.n := row_variable_bound g i j hj
    have h1 : naturalBob G j=G ⟨j,hjB⟩ := by simp only [naturalBob,hjB,↓reduceDIte]
    have h2 : indexedAliceObservable (transposePVM (P i)) j=
        outcomeObservable (transposePVM (P i)) ⟨j,hjB⟩ := indexedAliceObservable_fin _ ⟨j,hjB⟩
    change IsUnitary (naturalBob G j) ∧ IsUnitary (indexedAliceObservable (transposePVM (P i)) j)
    rw [h1,h2]
    exact ⟨CountProof.involution_unitary _ (usedBob_involution B hB _),
      CountProof.involution_unitary _ (outcomeObservable_involution _ _)⟩
  have hlocal : ∀ p ∈ L, hsNorm (p.1*s.psi-s.psi*p.2)≤theta g eps := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hjB : j<g.system.n := row_variable_bound g i j hj
    have h1 : naturalBob G j=G ⟨j,hjB⟩ := by simp only [naturalBob,hjB,↓reduceDIte]
    have h2 : indexedAliceObservable (transposePVM (P i)) j=
        outcomeObservable (transposePVM (P i)) ⟨j,hjB⟩ := indexedAliceObservable_fin _ ⟨j,hjB⟩
    change hsNorm (naturalBob G j*s.psi-s.psi*indexedAliceObservable (transposePVM (P i)) j)≤_
    rw [h1,h2]
    have h := prepared_generator_consistency s B P eps hB hBob hAlice heps hw i ⟨j,hjB⟩ hj
    rw [outcomeObservable_transpose] at h
    exact h
  have hvalid (a : Fin g.system.n → Bool) (ha : ¬validAnswer g i a) :
      (transposePVM (P i)).effects a=0 := by
    change ((P i).effects a).transpose=0
    rw [← hAlice i a,s.alice_valid i a ha]
    rfl
  have hpar : (L.map Prod.snd).prod=boolPhase (g.system.equations[i.val]).rhs • (1:Mat dA) := by
    simpa only [L,List.map_map,Function.comp_def] using alice_equation_product i (transposePVM (P i)) hvalid
  have hc : boolPhase (g.system.equations[i.val]).rhs*boolPhase (g.system.equations[i.val]).rhs=1 := by
    cases (g.system.equations[i.val]).rhs <;> norm_num [boolPhase]
  have hcn : ‖boolPhase (g.system.equations[i.val]).rhs‖=1 := by
    cases (g.system.equations[i.val]).rhs <;> norm_num [boolPhase]
  have h := linear_relation_bound s.psi L (theta g eps) hL hlocal _ hc hcn hpar
  simp only [L,List.map_map,Function.comp_def,List.length_map] at h
  exact h.trans (linear_transfer_constant g eps vars.length (g.arity_upper _ (List.getElem_mem i.isLt)))

end
end Companion.Analytic.TransferProof
