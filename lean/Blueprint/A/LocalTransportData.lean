import Blueprint.A.ShiftedExchange

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

def hostConj (W : Word) (x : FreeGroup Nat) : FreeGroup Nat := FreeGroup.mk W*x*(FreeGroup.mk W)⁻¹
def prototypeTau (m : Nat) : FreeGroup Nat := (FreeGroup.of 1)^m*FreeGroup.of 3*((FreeGroup.of 1)^m)⁻¹

theorem tau_exchange_single (n i m : Nat) (hn : 3≤n) (hi : i<n) (hm : m≤2)
    (W : Word) (hW : W.length≤30*n) (hWa : ∀ a∈W, a.1∈[1,2])
    (hWs : SmallPerm n 6 (pointHom (FreeGroup.mk W)))
    (he : pointHom (FreeGroup.mk W) (Concrete.Ray.one,m)=(Concrete.Ray.one,i)) :
    Close sourceRelator (hostConj W (prototypeTau m)) (FreeGroup.mk (tauWord i)) (localC n) := by
  have hU := single_length i n hi
  have hUs := small_perm_weaken (small_perm_omega 0 i n (by omega) hi) (by decide : 2≤4)
  have hpoint : pointHom (FreeGroup.mk W) (Concrete.Ray.one,m)=
      pointHom (FreeGroup.mk (singleWord i)) (Concrete.Ray.one,0) := by
    simpa only [singleWord,omega_permutation,Equiv.swap_apply_left] using he
  have h := transporter_exchange_shift n m hn hm (singleWord i) W (by omega) hW
    (omega_letters 0 i) hWa hUs hWs hpoint
  convert h using 1
  · simp only [hostConj,prototypeTau,←FreeGroup.mul_mk,mk_repeated_letter]
    change _=(FreeGroup.mk W*(FreeGroup.of 1)^m)*FreeGroup.of 3*(FreeGroup.mk W*(FreeGroup.of 1)^m)⁻¹
    group
  · simp only [tauWord,mk_transport]

theorem transvection_exchange (n i j : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) (hij : i≠j)
    (W : Word) (hW : W.length≤30*n) (hWa : ∀ a∈W, a.1∈[1,2])
    (hWs : SmallPerm n 6 (pointHom (FreeGroup.mk W)))
    (h0 : pointHom (FreeGroup.mk W) (Concrete.Ray.one,0)=(Concrete.Ray.one,j))
    (h1 : pointHom (FreeGroup.mk W) (Concrete.Ray.one,1)=(Concrete.Ray.one,i)) :
    Close sourceRelator (hostConj W (FreeGroup.of 4)) (FreeGroup.mk (transvectionWord i j)) (localC n) := by
  have hU := double_length i j n hn hi hj
  have hpoint : ∀ h, h<2 → pointHom (FreeGroup.mk W) (Concrete.Ray.one,h)=
      pointHom (FreeGroup.mk (doubleWord i j)) (Concrete.Ray.one,h) := by
    intro h hh
    have hc : h=0 ∨ h=1 := by omega
    rcases hc with rfl|rfl
    · simpa only [double_permutation,doublePerm_zero i j hij] using h0
    · simpa only [double_permutation,doublePerm_one] using h1
  have h := transporter_exchange_zero n 2 hn (Or.inr rfl) (doubleWord i j) W (by omega) hW
    (double_letters i j) hWa (small_perm_double i j n hn hi hj) hWs hpoint
  simpa only [hostConj,transvectionWord,mk_transport,show ¬(2:Nat)=1 by decide,↓reduceIte] using h

/-- An explicit common transporter for all three possible local coordinates. -/
theorem local_tuple_transporter (n i j k : Nat) (hn : 3≤n)
    (hi : i<n) (hj : j<n) (hk : k<n) (hij : i≠j) :
    ∃ W : Word, ∃ m : Nat, m≤2 ∧ (m=0 ↔ k=j) ∧ W.length≤30*n ∧
      (∀ a∈W, a.1∈[1,2]) ∧ SmallPerm n 6 (pointHom (FreeGroup.mk W)) ∧
      pointHom (FreeGroup.mk W) (Concrete.Ray.one,0)=(Concrete.Ray.one,j) ∧
      pointHom (FreeGroup.mk W) (Concrete.Ray.one,1)=(Concrete.Ray.one,i) ∧
      pointHom (FreeGroup.mk W) (Concrete.Ray.one,m)=(Concrete.Ray.one,k) := by
  have hdlen := double_length i j n hn hi hj
  have hds := small_perm_weaken (small_perm_double i j n hn hi hj) (by decide : 4≤6)
  have h0 : pointHom (FreeGroup.mk (doubleWord i j)) (Concrete.Ray.one,0)=(Concrete.Ray.one,j) := by
    rw [double_permutation,doublePerm_zero i j hij]
  have h1 : pointHom (FreeGroup.mk (doubleWord i j)) (Concrete.Ray.one,1)=(Concrete.Ray.one,i) := by
    rw [double_permutation,doublePerm_one]
  by_cases hkj : k=j
  · subst k
    exact ⟨doubleWord i j,0,by decide,by simp,by omega,double_letters i j,hds,h0,h1,h0⟩
  by_cases hki : k=i
  · subst k
    exact ⟨doubleWord i j,1,by decide,by simp [hij],by omega,double_letters i j,hds,h0,h1,h1⟩
  have ht := triple_positions i j k hij hki hkj
  refine ⟨tripleWord i j k,2,by decide,by simp [hkj],Nat.le_of_lt (triple_length i j k n hn hi hj hk),?_,
    small_perm_triple i j k n hn hi hj hk,ht.1,ht.2.1,ht.2.2⟩
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · exact double_letters i j a ha
  · exact omega_letters _ _ a ha

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.hostConj
#print axioms Blueprint.PairProof.prototypeTau
#print axioms Blueprint.PairProof.tau_exchange_single
#print axioms Blueprint.PairProof.transvection_exchange
#print axioms Blueprint.PairProof.local_tuple_transporter
