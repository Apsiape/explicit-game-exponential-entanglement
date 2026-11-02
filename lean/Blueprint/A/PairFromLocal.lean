import Blueprint.A.LocalFillingsProof
import Blueprint.A.HoughtonCorollary
import Blueprint.A.PairPresentation
import Blueprint.A.PairNumericBounds

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

theorem local_bounds (n : Nat) (hn : 3≤n) :
    let t : Fin n → FreeGroup Nat := fun i => FreeGroup.mk (tauWord i.val)
    let X : Fin n → Fin n → FreeGroup Nat := fun i j => FreeGroup.mk (transvectionWord i.val j.val)
    (∀ i, FiniteArea.Area sourceRelator (t i*t i) 1) ∧
    (∀ i j, FiniteArea.Area sourceRelator (groupComm (t i) (t j)) (localL n)) ∧
    (∀ i j, i≠j → ∀ k,
      Close sourceRelator (X i j*t k*(X i j)⁻¹) (Function.update t j (t j*t i) k) (localL n)) ∧
    (∀ i j, i≠j → ∀ a∈[5,6], FiniteArea.Area sourceRelator (groupComm (X i j) (FreeGroup.of a)) (localL n)) ∧
    (∀ i, ∀ a∈[5,6], ∀ b∈[5,6],
      FiniteArea.Area sourceRelator (groupComm (FreeGroup.of a) (t i*FreeGroup.of b*(t i)⁻¹)) (localL n)) := by
  classical
  obtain ⟨hsq,hcomm,hX,hlin,hnear⟩ := Published.localFillings n hn
  let H := FreeGroup.map encode
  have hm {w : FreeGroup Letter} {k : Nat} (h : FiniteArea.Area paperRelator w k) :
      FiniteArea.Area sourceRelator (H w) k :=
    area_map (S:=sourceRelator) H encode_decode_relator h
  have h4 : 4*localC n+1≤localL n := by dsimp [localC,localL]; omega
  have h5 : 5*localC n+1≤localL n := by dsimp [localC,localL]; omega
  have ht : ∀ i, H (paperTau i)=FreeGroup.mk (tauWord i) := mapped_tau
  have hx : ∀ i j, H (paperX i j)=FreeGroup.mk (transvectionWord i j) := mapped_X
  have ha : ∀ a : Fin 2, H (paperLamp a)=FreeGroup.of (a.val+5) := mapped_lamp
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    simpa only [map_mul,ht] using hm (hsq i)
  · intro i j
    by_cases hij : i=j
    · subst j
      have hg : ∀ z : FreeGroup Nat, groupComm z z=1 := by
        intro z
        dsimp [groupComm]
        group
      rw [hg]
      exact area_one sourceRelator (localL n)
    · simpa only [groupComm,map_mul,map_inv,ht] using area_weaken (hm (hcomm i j hij)) h4
  · intro i j hij k
    have hh := area_weaken (hm (hX i j hij k)) h5
    by_cases hk : k=j
    · subst k
      simpa only [Close,Function.update_self,↓reduceIte,map_mul,map_inv,ht,hx] using hh
    · simpa only [Close,Function.update_of_ne hk,hk,↓reduceIte,map_mul,map_inv,ht,hx] using hh
  · intro i j hij a ha'
    obtain ⟨a',rfl⟩ : ∃ a' : Fin 2, a=a'.val+5 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha'
      rcases ha' with rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
    have hb : 2*(doubleWord i.val j.val).length+1≤localL n := by
      have hh := double_length i.val j.val n hn i.isLt j.isLt
      dsimp [localL]
      omega
    simpa only [groupComm,map_mul,map_inv,hx,ha] using area_weaken (hm (hlin i j hij a')) hb
  · intro i a ha' b hb'
    obtain ⟨a',rfl⟩ : ∃ a' : Fin 2, a=a'.val+5 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha'
      rcases ha' with rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
    obtain ⟨b',rfl⟩ : ∃ b' : Fin 2, b=b'.val+5 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb'
      rcases hb' with rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
    have hb : 4*(singleWord i.val).length+1≤localL n := by
      have hh := single_length i.val n i.isLt
      dsimp [localL]
      omega
    simpa only [groupComm,map_mul,map_inv,ht,ha] using area_weaken (hm (hnear i a' b')) hb

theorem pair_areas_supported
    (N : Nat) (hN : 1≤N) : ∃ (T : (Fin N → Bool) → Word) (L : Nat),
    (∀ u, (T u).length≤21*N*max 3 N) ∧
    14000*N^2*max 3 N≤L ∧ (L:ℝ)≤(2:ℝ)^((log2 N+23)^2) ∧
    (∀ u v, u≠v → ∀ a∈[5,6], ∀ b∈[5,6],
      FiniteArea.Area sourceRelator (FreeGroup.mk (commWord (transportLamp (T u) a) (transportLamp (T v) b))) L) ∧
    (∀ u, FiniteArea.Area sourceRelator
      (FreeGroup.mk (T u++lampJ++FreeGroup.invRev (T u)++FreeGroup.invRev lampJ)) (4*(T u).length)) ∧
    (∀ u, ∀ a∈T u, 1≤a.1 ∧ a.1≤3) := by
  classical
  let n := max 3 N
  have hn : 3≤n := le_max_left _ _
  have hNn : N≤n := le_max_right _ _
  let emb : Fin N → Fin n := fun i => ⟨i.val,i.isLt.trans_le hNn⟩
  let t : Fin N → FreeGroup Nat := fun i => FreeGroup.mk (tauWord i.val)
  let X : Fin N → Fin N → FreeGroup Nat := fun i j => FreeGroup.mk (transvectionWord i.val j.val)
  let L0 := localL n
  let T := cubeWord N (fun i => tauWord i.val)
  obtain ⟨hsq,hcomm,hX,hlin,hnear⟩ := local_bounds n hn
  have hE : Function.Injective emb := fun i j h => Fin.ext (congrArg (fun x : Fin n => x.val) h)
  have hL0 : 1≤L0 := by dsimp [L0,localL]; omega
  have hsq' : ∀ i, FiniteArea.Area sourceRelator (t i*t i) 1 := fun i => hsq (emb i)
  have hcomm' : ∀ i j, FiniteArea.Area sourceRelator (groupComm (t i) (t j)) L0 :=
    fun i j => hcomm (emb i) (emb j)
  have hX' : ∀ i j, i≠j → ∀ k,
      Close sourceRelator (X i j*t k*(X i j)⁻¹) (Function.update t j (t j*t i) k) L0 := by
    intro i j hij k
    have hh := hX (emb i) (emb j) (fun he => hij (hE he)) (emb k)
    by_cases hk : k=j
    · subst k
      simpa only [Function.update_self] using hh
    · simpa only [Function.update_of_ne hk,Function.update_of_ne (fun he => hk (hE he))] using hh
  refine ⟨T,100*N^3*L0,?_,?_,?_,?_,?_,?_⟩
  · intro u
    have hh := cubeWord_length N (21*n) (fun i => tauWord i.val) u
      (fun i => tau_length i.val n (i.isLt.trans_le hNn))
    simpa only [T,Nat.mul_left_comm,Nat.mul_assoc] using hh
  · have hL : 700*n≤L0 := by dsimp [L0,localL]; omega
    change 14000*N^2*n≤100*N^3*L0
    have hP : N^2≤N^3 := Nat.pow_le_pow_right hN (by omega)
    nlinarith [Nat.mul_le_mul_left (100*N^3) hL,
      Nat.mul_le_mul_right (70000*n) hP]
  · apply pair_numeric_bound N L0 hN
    have hd := Published.houghtonDehnCorollary (1500*n) (by omega)
    have hh : (dehnH (1500*n):ℝ)≤(2:ℝ)^((log2 (1500*n)+6)^2) := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using
        (Nat.cast_le.mpr hd.2.2.1).trans hd.2.2.2
    dsimp [L0,localL,n]
    push_cast
    dsimp [n] at hh
    push_cast at hh
    linarith
  · intro u v huv a ha b hb
    have hh := pair_area_bound N L0 hN hL0 t X hsq' hcomm' hX'
      (FreeGroup.of a) (FreeGroup.of b)
      (fun i j hij => hlin (emb i) (emb j) (fun he => hij (hE he)) a ha)
      (fun i j hij => hlin (emb i) (emb j) (fun he => hij (hE he)) b hb)
      (fun j => hnear (emb j) a ha b hb) u v huv
    simpa only [mk_word_comm,mk_transport,T,mk_cubeWord,t] using hh
  · intro u
    exact lampJ_transport_area (T u) (cubeWord_letters N _ u _
      (fun i a ha => by
        have hh := tau_letters i.val a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
        omega))
  · intro u
    exact cubeWord_letters N _ u _ (fun i a ha => by
      have hh := tau_letters i.val a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      omega)

theorem pair_areas_from_local
    (N : Nat) (hN : 1≤N) : ∃ (T : (Fin N → Bool) → Word) (L : Nat),
    (∀ u, (T u).length≤21*N*max 3 N) ∧
    14000*N^2*max 3 N≤L ∧ (L:ℝ)≤(2:ℝ)^((log2 N+23)^2) ∧
    (∀ u v, u≠v → ∀ a∈[5,6], ∀ b∈[5,6],
      FiniteArea.Area sourceRelator (FreeGroup.mk (commWord (transportLamp (T u) a) (transportLamp (T v) b))) L) ∧
    (∀ u, FiniteArea.Area sourceRelator
      (FreeGroup.mk (T u++lampJ++FreeGroup.invRev (T u)++FreeGroup.invRev lampJ)) (4*(T u).length)) := by
  obtain ⟨T,L,h1,h2,h3,h4,h5,_⟩ := pair_areas_supported N hN
  exact ⟨T,L,h1,h2,h3,h4,h5⟩

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.local_bounds
#print axioms Blueprint.PairProof.pair_areas_supported
#print axioms Blueprint.PairProof.pair_areas_from_local
