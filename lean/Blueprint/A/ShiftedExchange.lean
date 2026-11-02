import Blueprint.A.TransporterExchange

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

theorem transporter_exchange_zero (n k : Nat) (hn : 3≤n) (hk : k=1 ∨ k=2)
    (U W : Word) (hU : U.length≤30*n) (hW : W.length≤30*n)
    (hUa : ∀ a∈U, a.1∈[1,2]) (hWa : ∀ a∈W, a.1∈[1,2])
    (hUs : SmallPerm n 4 (pointHom (FreeGroup.mk U)))
    (hWs : SmallPerm n 6 (pointHom (FreeGroup.mk W)))
    (he : ∀ h, h<k → pointHom (FreeGroup.mk W) (Concrete.Ray.one,h)=
      pointHom (FreeGroup.mk U) (Concrete.Ray.one,h)) :
    Close sourceRelator
      (FreeGroup.mk W*FreeGroup.of (if k=1 then 3 else 4)*(FreeGroup.mk W)⁻¹)
      (FreeGroup.mk U*FreeGroup.of (if k=1 then 3 else 4)*(FreeGroup.mk U)⁻¹) (localC n) := by
  let g := (pointHom (FreeGroup.mk W))⁻¹*pointHom (FreeGroup.mk U)
  have hg : SmallPerm n 10 g := small_perm_mul (small_perm_inv hWs) hUs
  have hf : ∀ h, h<k → g (Concrete.Ray.one,h)=(Concrete.Ray.one,h) := by
    intro h hh
    dsimp [g,Equiv.Perm.mul_apply]
    rw [←he h hh]
    exact (pointHom (FreeGroup.mk W)).symm_apply_apply _
  obtain ⟨v,hv,hvpoint⟩ := small_stabilizer_word k n 10 hk g hg hf
  exact transporter_exchange_word n k hn hk U W v hU (by omega) hUa hWa (by omega) hvpoint

def shiftCorrection (j : Nat) : Equiv.Perm Concrete.Point :=
  (pointHom houghtonS*Concrete.pPoint)^j*(Concrete.pPoint^j)⁻¹

theorem shift_correction_small (n j : Nat) (hn : 3≤n) (hj : j≤2) :
    SmallPerm n 3 (shiftCorrection j) := by
  refine ⟨{(Concrete.Ray.one,0),(Concrete.Ray.one,1),(Concrete.Ray.one,2)},by decide,?_,?_⟩
  · intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl|rfl|rfl <;> exact ⟨rfl,by omega⟩
  · intro y hy
    obtain ⟨r,h⟩ := y
    have hj' : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj' with rfl|rfl|rfl
    all_goals
      cases r <;> rcases h with _|_|_|h
      all_goals first | (exact (hy rfl).elim) | (simp)

theorem transporter_exchange_shift (n j : Nat) (hn : 3≤n) (hj : j≤2)
    (U W0 : Word) (hU : U.length≤30*n) (hW : W0.length≤30*n)
    (hUa : ∀ a∈U, a.1∈[1,2]) (hWa : ∀ a∈W0, a.1∈[1,2])
    (hUs : SmallPerm n 4 (pointHom (FreeGroup.mk U)))
    (hWs : SmallPerm n 6 (pointHom (FreeGroup.mk W0)))
    (he : pointHom (FreeGroup.mk W0) (Concrete.Ray.one,j)=
      pointHom (FreeGroup.mk U) (Concrete.Ray.one,0)) :
    Close sourceRelator
      (FreeGroup.mk (W0++List.replicate j (1,true))*FreeGroup.of 3*
        (FreeGroup.mk (W0++List.replicate j (1,true)))⁻¹)
      (FreeGroup.mk U*FreeGroup.of 3*(FreeGroup.mk U)⁻¹) (localC n) := by
  let W := W0++List.replicate j (1,true)
  let P := Concrete.pPoint
  let S := pointHom houghtonS
  let H := (pointHom (FreeGroup.mk W0))⁻¹*pointHom (FreeGroup.mk U)
  let G := (pointHom (FreeGroup.mk W))⁻¹*pointHom (FreeGroup.mk U)
  let gp := shiftCorrection j*H
  have hWpoint : pointHom (FreeGroup.mk W)=pointHom (FreeGroup.mk W0)*P^j := by
    simp only [W,←FreeGroup.mul_mk,mk_repeated_letter,map_mul,map_pow]
    rfl
  have hgsmall : SmallPerm n 13 gp :=
    small_perm_mul (shift_correction_small n j hn hj) (small_perm_mul (small_perm_inv hWs) hUs)
  have hGfix : G (Concrete.Ray.one,0)=(Concrete.Ray.one,0) := by
    have hsame : pointHom (FreeGroup.mk W) (Concrete.Ray.one,0)=pointHom (FreeGroup.mk U) (Concrete.Ray.one,0) := by
      rw [hWpoint,Equiv.Perm.mul_apply]
      simpa only [P,HoughtonProof.pPoint_pow_one,Nat.zero_add] using he
    dsimp [G,Equiv.Perm.mul_apply]
    rw [←hsame]
    exact (pointHom (FreeGroup.mk W)).symm_apply_apply _
  have hgp : gp=(S*P)^j*G := by
    dsimp [gp,shiftCorrection,H,G]
    rw [hWpoint]
    dsimp only [S,P]
    group
  have hgfix : ∀ h, h<1 → gp (Concrete.Ray.one,h)=(Concrete.Ray.one,h) := by
    intro h hh
    have hh0 : h=0 := by omega
    subst h
    rw [hgp,Equiv.Perm.mul_apply,hGfix,spPoint_power_zero]
  obtain ⟨w,hw,hwp⟩ := small_stabilizer_word 1 n 13 (Or.inl rfl) gp hgsmall hgfix
  let v : Word := List.replicate j (1,false)++w
  have hv : v.length≤122*n := by simp only [v,List.length_append,List.length_replicate]; omega
  have hgen : pointHom (stabilizerHom 1 (FreeGroup.mk [(1,true)]))=S*P := rfl
  have hneg : pointHom (stabilizerHom 1 (FreeGroup.mk [(1,false)]))=(S*P)⁻¹ := by
    change pointHom (stabilizerHom 1 (FreeGroup.of 1)⁻¹)=_
    rw [map_inv,map_inv]
    exact congrArg Inv.inv hgen
  have hvp : pointHom (stabilizerHom 1 (FreeGroup.mk v))=G := by
    simp only [v,←FreeGroup.mul_mk,mk_repeated_letter,map_mul,map_pow,hneg,hwp,hgp,inv_pow,inv_mul_cancel_left]
  apply transporter_exchange_word n 1 hn (Or.inl rfl) U W v hU _ hUa _ hv hvp
  · simp only [W,List.length_append,List.length_replicate]; omega
  · intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hWa a ha
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp ha
      simp

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.transporter_exchange_zero
#print axioms Blueprint.PairProof.shiftCorrection
#print axioms Blueprint.PairProof.shift_correction_small
#print axioms Blueprint.PairProof.transporter_exchange_shift
