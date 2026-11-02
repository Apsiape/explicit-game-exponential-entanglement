import Blueprint.A.FiniteStabilizer
import Blueprint.A.TransportPermutations
import Blueprint.A.HoughtonCertificate

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

theorem invRev_letters (w : Word) (P : Nat → Prop) (hw : ∀ a∈w, P a.1) :
    ∀ a∈FreeGroup.invRev w, P a.1 := by
  intro a ha
  simp only [FreeGroup.invRev,List.mem_map,List.mem_reverse] at ha
  obtain ⟨b,hb,he⟩ := ha
  have hh := congrArg Prod.fst he
  change b.1=a.1 at hh
  rw [←hh]
  exact hw b hb

theorem stabilizer_letters (k : Nat) (hk : k=1 ∨ k=2) (w : Word) :
    ∀ a∈stabilizerExpand k w, a.1∈[1,2] := by
  intro a ha
  simp only [stabilizerExpand,List.mem_flatten,List.mem_map] at ha
  obtain ⟨v,⟨b,hb,rfl⟩,ha⟩ := ha
  have hword (j : Nat) (hj : j=1 ∨ j=2) : ∀ a∈stabilizerWord k j, a.1∈[1,2] := by
    rcases hk with rfl|rfl <;> rcases hj with rfl|rfl <;> decide
  simp only [stabilizerLetter] at ha
  split at ha
  · rename_i hj
    split at ha
    · exact hword b.1 hj a ha
    · exact invRev_letters _ _ (hword b.1 hj) a ha
  · simp at ha

theorem small_stabilizer_word (k n m : Nat) (hk : k=1 ∨ k=2)
    (g : Equiv.Perm Concrete.Point) (hg : SmallPerm n m g)
    (hfix : ∀ h, h<k → g (Concrete.Ray.one,h)=(Concrete.Ray.one,h)) :
    ∃ w : Word, w.length≤10*n*(m-1) ∧ pointHom (stabilizerHom k (FreeGroup.mk w))=g := by
  obtain ⟨S,hSc,hS,hg⟩ := hg
  let T := S.filter (fun y => k≤y.2)
  have hT : ∀ y, g y≠y → y∈T := by
    intro y hy
    have hs := hg y hy
    have hr := (hS y hs).1
    have hh : k≤y.2 := by
      by_contra hn
      apply hy
      have hf := hfix y.2 (by omega)
      simpa only [←hr,Prod.mk.eta] using hf
    exact Finset.mem_filter.mpr ⟨hs,hh⟩
  obtain ⟨w,hw,ha,he⟩ := finite_stabilizer_word k n hk T g hT (by
    intro y hy
    have ht := Finset.mem_filter.mp hy
    exact ⟨(hS y ht.1).1,ht.2,(hS y ht.1).2⟩)
  have hc : T.card≤m := (Finset.card_filter_le _ _).trans hSc
  exact ⟨w,hw.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hc 1)),he⟩

/-- Charged transporter replacement from an actual stabilizer word. The
Houghton null word is filled by the proved, fixed-presentation Dehn bound. -/
theorem transporter_exchange_word (n k : Nat) (hn : 3≤n) (hk : k=1 ∨ k=2)
    (U W v : Word) (hU : U.length≤30*n) (hW : W.length≤30*n+2)
    (hUa : ∀ a∈U, a.1∈[1,2]) (hWa : ∀ a∈W, a.1∈[1,2])
    (hv : v.length≤122*n)
    (he : pointHom (stabilizerHom k (FreeGroup.mk v))=
      (pointHom (FreeGroup.mk W))⁻¹*pointHom (FreeGroup.mk U)) :
    Close sourceRelator
      (FreeGroup.mk W*FreeGroup.of (if k=1 then 3 else 4)*(FreeGroup.mk W)⁻¹)
      (FreeGroup.mk U*FreeGroup.of (if k=1 then 3 else 4)*(FreeGroup.mk U)⁻¹) (localC n) := by
  let Z := stabilizerExpand k v
  let omega := FreeGroup.invRev W++U++FreeGroup.invRev Z
  have hlen : omega.length≤1500*n := by
    have hz := stabilizer_length k hk v
    simp only [omega,List.length_append,FreeGroup.invRev_length]
    dsimp [Z] at *
    omega
  have hletters : ∀ a∈omega, a.1∈[1,2] := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_append.mp ha with ha|ha
      · exact invRev_letters W _ hWa a ha
      · exact hUa a ha
    · exact invRev_letters Z _ (stabilizer_letters k hk v) a ha
  have hnull : pointHom (FreeGroup.mk omega)=1 := by
    simp only [omega,←FreeGroup.mul_mk,←FreeGroup.inv_mk,map_mul,map_inv,Z,stabilizer_mk,he]
    group
  have harea := houghton_certificate_area omega (1500*n) (by omega) hlen hletters hnull
  have hz : Close sourceRelator ((FreeGroup.mk W)⁻¹*FreeGroup.mk U)
      (stabilizerHom k (FreeGroup.mk v)) (dehnH (1500*n)) := by
    simpa only [Close,omega,←FreeGroup.mul_mk,←FreeGroup.inv_mk,Z,stabilizer_mk] using harea
  have hc := close_conjugator (FreeGroup.of (if k=1 then 3 else 4)) hz
  have hs : Close sourceRelator
      (stabilizerHom k (FreeGroup.mk v)*FreeGroup.of (if k=1 then 3 else 4)*
        (stabilizerHom k (FreeGroup.mk v))⁻¹) (FreeGroup.of (if k=1 then 3 else 4)) v.length :=
    stabilizer_word_comm k hk v
  have hh := close_symm (close_conj (FreeGroup.mk W) (close_trans hc hs))
  have hb : 2*dehnH (1500*n)+v.length≤localC n := by dsimp [localC]; omega
  apply close_weaken (k:=2*dehnH (1500*n)+v.length) _ hb
  convert hh using 1; group

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.invRev_letters
#print axioms Blueprint.PairProof.stabilizer_letters
#print axioms Blueprint.PairProof.small_stabilizer_word
#print axioms Blueprint.PairProof.transporter_exchange_word
