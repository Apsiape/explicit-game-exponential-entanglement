import Blueprint.A.OmegaPermutation
import Blueprint.A.FiniteSwapWords

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

def SmallPerm (n m : Nat) (g : Equiv.Perm Concrete.Point) : Prop :=
  ∃ S : Finset Concrete.Point, S.card≤m ∧
    (∀ y∈S, y.1=Concrete.Ray.one ∧ y.2<n) ∧ (∀ y, g y≠y → y∈S)

theorem small_perm_weaken {n m l : Nat} {g : Equiv.Perm Concrete.Point}
    (hg : SmallPerm n m g) (hm : m≤l) : SmallPerm n l g := by
  obtain ⟨S,hSc,hS,hg⟩ := hg
  exact ⟨S,hSc.trans hm,hS,hg⟩

theorem small_perm_one (n m : Nat) : SmallPerm n m 1 := by
  refine ⟨∅,by simp,by simp,?_⟩
  intro y hy
  exact (hy rfl).elim

theorem small_perm_mul {n m l : Nat} {g h : Equiv.Perm Concrete.Point}
    (hg : SmallPerm n m g) (hh : SmallPerm n l h) : SmallPerm n (m+l) (g*h) := by
  obtain ⟨S,hSc,hS,hg⟩ := hg
  obtain ⟨T,hTc,hT,hh⟩ := hh
  refine ⟨S∪T,(Finset.card_union_le S T).trans (Nat.add_le_add hSc hTc),?_,finite_support_mul g h S T hg hh⟩
  intro y hy
  exact (Finset.mem_union.mp hy).elim (hS y) (hT y)

theorem small_perm_inv {n m : Nat} {g : Equiv.Perm Concrete.Point}
    (hg : SmallPerm n m g) : SmallPerm n m g⁻¹ := by
  obtain ⟨S,hSc,hS,hg⟩ := hg
  exact ⟨S,hSc,hS,finite_support_inv g S hg⟩

theorem small_perm_omega (i j n : Nat) (hi : i<n) (hj : j<n) :
    SmallPerm n 2 (pointHom (FreeGroup.mk (omegaWord i j))) := by
  rw [omega_permutation]
  refine ⟨{(Concrete.Ray.one,i),(Concrete.Ray.one,j)},(Finset.card_insert_le _ _).trans (by simp),?_,?_⟩
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact ⟨rfl,hi⟩
    · rw [Finset.mem_singleton] at hy
      subst y
      exact ⟨rfl,hj⟩
  · intro y hy
    by_contra hn
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    exact hy (Equiv.swap_apply_of_ne_of_ne hn.1 hn.2)

theorem nat_swap_lt (a b x n : Nat) (ha : a<n) (hb : b<n) (hx : x<n) :
    Equiv.swap a b x<n := by
  by_cases hxa : x=a
  · subst x; simpa using hb
  by_cases hxb : x=b
  · subst x; simpa using ha
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  exact hx

theorem ray_swap (a b x : Nat) :
    Equiv.swap (Concrete.Ray.one,a) (Concrete.Ray.one,b) (Concrete.Ray.one,x)=
      (Concrete.Ray.one,Equiv.swap a b x) := by
  simp only [Equiv.swap_apply_def,Prod.mk.injEq,true_and]
  split_ifs <;> rfl

def doublePerm (i j : Nat) : Equiv.Perm Nat := Equiv.swap 0 j*Equiv.swap 1 (Equiv.swap 0 j i)

theorem double_permutation (i j h : Nat) :
    pointHom (FreeGroup.mk (doubleWord i j)) (Concrete.Ray.one,h)=
      (Concrete.Ray.one,doublePerm i j h) := by
  simp only [doubleWord,←FreeGroup.mul_mk,map_mul,omega_permutation,Equiv.Perm.mul_apply,ray_swap,doublePerm]

theorem doublePerm_zero (i j : Nat) (hij : i≠j) : doublePerm i j 0=j := by
  dsimp [doublePerm,Equiv.Perm.mul_apply]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem doublePerm_one (i j : Nat) : doublePerm i j 1=i := by
  change Equiv.swap 0 j (Equiv.swap 1 (Equiv.swap 0 j i) 1)=i
  rw [Equiv.swap_apply_left,Equiv.swap_apply_self]

theorem small_perm_double (i j n : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) :
    SmallPerm n 4 (pointHom (FreeGroup.mk (doubleWord i j))) := by
  have h := small_perm_mul (small_perm_omega 0 j n (by omega) hj)
    (small_perm_omega 1 (Equiv.swap 0 j i) n (by omega) (nat_swap_lt 0 j i n (by omega) hj hi))
  simpa only [doubleWord,←FreeGroup.mul_mk,map_mul] using h

def tripleWord (i j k : Nat) : Word :=
  doubleWord i j ++ omegaWord 2 ((doublePerm i j)⁻¹ k)

theorem doublePerm_inverse_lt (i j k n : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) (hk : k<n) :
    (doublePerm i j)⁻¹ k<n := by
  change Equiv.swap 1 (Equiv.swap 0 j i) (Equiv.swap 0 j k)<n
  exact nat_swap_lt 1 _ _ n (by omega) (nat_swap_lt 0 j i n (by omega) hj hi)
    (nat_swap_lt 0 j k n (by omega) hj hk)

theorem triple_length (i j k n : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) (hk : k<n) :
    (tripleWord i j k).length<30*n := by
  have h1 := double_length i j n hn hi hj
  have h2 := omega_length 2 ((doublePerm i j)⁻¹ k) n (by omega) (doublePerm_inverse_lt i j k n hn hi hj hk)
  simp only [tripleWord,List.length_append]
  omega

theorem small_perm_triple (i j k n : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) (hk : k<n) :
    SmallPerm n 6 (pointHom (FreeGroup.mk (tripleWord i j k))) := by
  simpa only [tripleWord,←FreeGroup.mul_mk,map_mul] using
    small_perm_mul (small_perm_double i j n hn hi hj)
      (small_perm_omega 2 ((doublePerm i j)⁻¹ k) n (by omega) (doublePerm_inverse_lt i j k n hn hi hj hk))

theorem triple_permutation (i j k h : Nat) :
    pointHom (FreeGroup.mk (tripleWord i j k)) (Concrete.Ray.one,h)=
      (Concrete.Ray.one,doublePerm i j (Equiv.swap 2 ((doublePerm i j)⁻¹ k) h)) := by
  simp only [tripleWord,←FreeGroup.mul_mk,map_mul,Equiv.Perm.mul_apply,omega_permutation,ray_swap,double_permutation]

theorem triple_positions (i j k : Nat) (hij : i≠j) (hki : k≠i) (hkj : k≠j) :
    pointHom (FreeGroup.mk (tripleWord i j k)) (Concrete.Ray.one,0)=(Concrete.Ray.one,j) ∧
    pointHom (FreeGroup.mk (tripleWord i j k)) (Concrete.Ray.one,1)=(Concrete.Ray.one,i) ∧
    pointHom (FreeGroup.mk (tripleWord i j k)) (Concrete.Ray.one,2)=(Concrete.Ray.one,k) := by
  have h0 : (doublePerm i j)⁻¹ k≠0 := by
    intro he
    apply hkj
    exact ((doublePerm i j).apply_symm_apply k).symm.trans ((congrArg (doublePerm i j) he).trans (doublePerm_zero i j hij))
  have h1 : (doublePerm i j)⁻¹ k≠1 := by
    intro he
    apply hki
    exact ((doublePerm i j).apply_symm_apply k).symm.trans ((congrArg (doublePerm i j) he).trans (doublePerm_one i j))
  simp only [triple_permutation,Equiv.swap_apply_of_ne_of_ne (by decide : (0:Nat)≠2) h0.symm,
    Equiv.swap_apply_of_ne_of_ne (by decide : (1:Nat)≠2) h1.symm,
    doublePerm_zero i j hij,doublePerm_one,Equiv.swap_apply_left]
  exact ⟨trivial,trivial,congrArg (fun h => (Concrete.Ray.one,h)) ((doublePerm i j).apply_symm_apply k)⟩

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.SmallPerm
#print axioms Blueprint.PairProof.small_perm_weaken
#print axioms Blueprint.PairProof.small_perm_one
#print axioms Blueprint.PairProof.small_perm_mul
#print axioms Blueprint.PairProof.small_perm_inv
#print axioms Blueprint.PairProof.small_perm_omega
#print axioms Blueprint.PairProof.nat_swap_lt
#print axioms Blueprint.PairProof.ray_swap
#print axioms Blueprint.PairProof.doublePerm
#print axioms Blueprint.PairProof.double_permutation
#print axioms Blueprint.PairProof.doublePerm_zero
#print axioms Blueprint.PairProof.doublePerm_one
#print axioms Blueprint.PairProof.small_perm_double
#print axioms Blueprint.PairProof.tripleWord
#print axioms Blueprint.PairProof.doublePerm_inverse_lt
#print axioms Blueprint.PairProof.triple_length
#print axioms Blueprint.PairProof.small_perm_triple
#print axioms Blueprint.PairProof.triple_permutation
#print axioms Blueprint.PairProof.triple_positions
