import Blueprint.A.LocalTransportData

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

theorem prototype_commuting : FiniteArea.Area sourceRelator
    (groupComm (prototypeTau 0) (prototypeTau 1)) 1 := by
  convert source_area ⟨9,by decide⟩ using 1; decide +kernel

theorem prototype_action (m : Nat) (hm : m≤2) :
    Close sourceRelator (FreeGroup.of 4*prototypeTau m*(FreeGroup.of 4)⁻¹)
      (if m=0 then prototypeTau 0*prototypeTau 1 else prototypeTau m) 1 := by
  unfold Close
  have hh : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hh with rfl|rfl|rfl
  · convert source_area ⟨10,by decide⟩ using 1; decide +kernel
  · convert source_area ⟨11,by decide⟩ using 1; decide +kernel
  · convert source_area ⟨12,by decide⟩ using 1; decide +kernel

theorem source_tau_commuting (n i j : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) (hij : i≠j) :
    FiniteArea.Area sourceRelator (groupComm (FreeGroup.mk (tauWord i)) (FreeGroup.mk (tauWord j)))
      (4*localC n+1) := by
  let W := doubleWord j i
  have hW : W.length≤30*n := by
    dsimp only [W]
    have := double_length j i n hn hj hi
    omega
  have hWs : SmallPerm n 6 (pointHom (FreeGroup.mk W)) :=
    small_perm_weaken (small_perm_double j i n hn hj hi) (by decide)
  have h0 : pointHom (FreeGroup.mk W) (Concrete.Ray.one,0)=(Concrete.Ray.one,i) := by
    rw [double_permutation,doublePerm_zero j i hij.symm]
  have h1 : pointHom (FreeGroup.mk W) (Concrete.Ray.one,1)=(Concrete.Ray.one,j) := by
    rw [double_permutation,doublePerm_one]
  have ht0 := tau_exchange_single n i 0 hn hi (by decide) W hW (double_letters j i) hWs h0
  have ht1 := tau_exchange_single n j 1 hn hj (by decide) W hW (double_letters j i) hWs h1
  have hc := close_symm (close_comm ht0 ht1)
  have hb : FiniteArea.Area sourceRelator
      (groupComm (hostConj W (prototypeTau 0)) (hostConj W (prototypeTau 1))) 1 := by
    convert area_conj (FreeGroup.mk W) prototype_commuting using 1
    simp only [hostConj,groupComm]
    group
  have hh := close_to_one.mp (close_trans hc (close_to_one.mpr hb))
  convert hh using 1; omega

theorem source_transvection_action (n i j k : Nat) (hn : 3≤n)
    (hi : i<n) (hj : j<n) (hk : k<n) (hij : i≠j) :
    FiniteArea.Area sourceRelator
      (FreeGroup.mk (transvectionWord i j)*FreeGroup.mk (tauWord k)*(FreeGroup.mk (transvectionWord i j))⁻¹*
        (if k=j then FreeGroup.mk (tauWord j)*FreeGroup.mk (tauWord i) else FreeGroup.mk (tauWord k))⁻¹)
      (5*localC n+1) := by
  obtain ⟨W,m,hm,hm0,hW,hWa,hWs,h0,h1,hkpos⟩ := local_tuple_transporter n i j k hn hi hj hk hij
  have hX := transvection_exchange n i j hn hi hj hij W hW hWa hWs h0 h1
  have ht := tau_exchange_single n k m hn hk hm W hW hWa hWs hkpos
  let B := if m=0 then hostConj W (prototypeTau 0)*hostConj W (prototypeTau 1) else hostConj W (prototypeTau m)
  let D := if k=j then FreeGroup.mk (tauWord j)*FreeGroup.mk (tauWord i) else FreeGroup.mk (tauWord k)
  have hr : Close sourceRelator B D (2*localC n) := by
    by_cases hmz : m=0
    · have hkj := hm0.mp hmz
      have ht0 := tau_exchange_single n j 0 hn hj (by decide) W hW hWa hWs h0
      have ht1 := tau_exchange_single n i 1 hn hi (by decide) W hW hWa hWs h1
      simpa only [B,D,hmz,hkj,↓reduceIte,show localC n+localC n=2*localC n by omega] using close_mul ht0 ht1
    · have hkj : k≠j := fun he => hmz (hm0.mpr he)
      simpa only [B,D,hmz,hkj,↓reduceIte] using close_weaken ht (by omega : localC n≤2*localC n)
  have hb : Close sourceRelator
      (hostConj W (FreeGroup.of 4)*hostConj W (prototypeTau m)*(hostConj W (FreeGroup.of 4))⁻¹) B 1 := by
    have hh := close_conj (FreeGroup.mk W) (prototype_action m hm)
    convert hh using 1
    · simp only [hostConj]
      group
    · by_cases hmz : m=0
      · simp only [B,hmz,↓reduceIte]
        simp only [hostConj]
        group
      · simp only [B,hmz,↓reduceIte,hostConj]
  have hl := close_mul (close_mul hX ht) (close_inv hX)
  have hh := close_trans (close_trans (close_symm hl) hb) hr
  have hcost : localC n+localC n+localC n+1+2*localC n=5*localC n+1 := by omega
  simpa only [Close,D,hcost] using hh

end
end Blueprint.PairProof

namespace Blueprint.Published
noncomputable section
open Companion ASector PairProof

/-- Lemma 7.7(a)--(d), with the exact original transporter words and cell bounds. -/
theorem localFillings : LocalFillings := by
  intro n hn
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact paper_tau_square i.val
  · intro i j hij
    have hnij : i.val≠j.val := fun he => hij (Fin.ext he)
    have hh := source_area_to_paper (source_tau_commuting n i.val j.val hn i.isLt j.isLt hnij)
    simpa only [groupComm,map_mul,map_inv,paperTau] using hh
  · intro i j hij k
    have hnij : i.val≠j.val := fun he => hij (Fin.ext he)
    have hh := source_area_to_paper (source_transvection_action n i.val j.val k.val hn i.isLt j.isLt k.isLt hnij)
    simpa only [map_mul,map_inv,apply_ite,paperTau,paperX,Fin.val_inj] using hh
  · intro i j hij a
    exact paper_transvection_lamp i.val j.val a
  · intro i a b
    exact paper_translated_neighbour i.val a b

end
end Blueprint.Published

#print axioms Blueprint.PairProof.prototype_commuting
#print axioms Blueprint.PairProof.prototype_action
#print axioms Blueprint.PairProof.source_tau_commuting
#print axioms Blueprint.PairProof.source_transvection_action
#print axioms Blueprint.Published.localFillings
