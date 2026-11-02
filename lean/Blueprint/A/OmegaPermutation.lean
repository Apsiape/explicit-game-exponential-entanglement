import Blueprint.A.LocalBasic
import Blueprint.A.HoughtonPermutation

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published HoughtonProof

theorem mk_repeated_word (w : Word) (n : Nat) :
    FreeGroup.mk (List.replicate n w).flatten=(FreeGroup.mk w)^n := by
  induction n with
  | zero => simp [←FreeGroup.one_eq_mk]
  | succ n ih => simp only [List.replicate_succ,List.flatten_cons,←FreeGroup.mul_mk,ih,pow_succ']

theorem point_s_swap : pointHom houghtonS=
    Equiv.swap (Concrete.Ray.one,0) (Concrete.Ray.one,1) :=
  johnsonAlpha_swap

theorem mk_repeated_letter (a : Nat × Bool) (n : Nat) :
    FreeGroup.mk (List.replicate n a)=(FreeGroup.mk [a])^n := by
  induction n with
  | zero => simp [←FreeGroup.one_eq_mk]
  | succ n ih =>
    change FreeGroup.mk ([a]++List.replicate n a)=_
    rw [←FreeGroup.mul_mk,ih,pow_succ']

theorem spPoint_power_zero (n : Nat) :
    ((pointHom houghtonS*Concrete.pPoint)^n) (Concrete.Ray.one,0)=(Concrete.Ray.one,0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,ih,Equiv.Perm.mul_apply,point_s_swap]; rfl

theorem spPoint_power_one (n : Nat) :
    ((pointHom houghtonS*Concrete.pPoint)^n) (Concrete.Ray.one,1)=(Concrete.Ray.one,n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,Equiv.Perm.mul_apply,point_s_swap]
    change Equiv.swap (Concrete.Ray.one,0) (Concrete.Ray.one,1) (Concrete.Ray.one,n+2)=_
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp

theorem omega_permutation (i j : Nat) : pointHom (FreeGroup.mk (omegaWord i j))=
    Equiv.swap (Concrete.Ray.one,i) (Concrete.Ray.one,j) := by
  by_cases he : i=j
  · subst j; simp [omegaWord,←FreeGroup.one_eq_mk]; rfl
  let l := min i j
  let d := max i j-l-1
  let S := pointHom houghtonS
  let P := Concrete.pPoint
  have hs : S*S=1 := by simp [S,point_s_swap]
  have hrev (n : Nat) : (S*P⁻¹)^n*S=S*((S*P)^n)⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,pow_succ',mul_inv_rev]
      calc
        _=(S*P⁻¹)^n*S*P⁻¹*S := by group
        _=S*((S*P)^n)⁻¹*P⁻¹*S := by rw [ih]
        _=S*((S*P)^n)⁻¹*(S*P)⁻¹ := by
          have hSi : S⁻¹=S := inv_eq_of_mul_eq_one_right hs
          simp only [mul_inv_rev,hSi,mul_assoc]
  have hword : pointHom (FreeGroup.mk (omegaWord i j))=
      (P^l*(S*P)^d)*S*(P^l*(S*P)^d)⁻¹ := by
    simp only [omegaWord,he,↓reduceIte,←FreeGroup.mul_mk,mk_repeated_word,mk_repeated_letter,map_mul,map_pow,
      ←show houghtonS=FreeGroup.mk [(1,true),(2,true),(1,false),(2,false)] by rfl]
    change P^l*(S*P)^d*(S*P⁻¹)^d*S*(P⁻¹)^l=_
    rw [mul_assoc (P^l*(S*P)^d),hrev]
    group
  have h0 : (P^l*(pointHom houghtonS*P)^d) (Concrete.Ray.one,0)=(Concrete.Ray.one,l) := by
    rw [Equiv.Perm.mul_apply,spPoint_power_zero]
    simpa only [Nat.zero_add] using pPoint_pow_one l 0
  have h1 : (P^l*(pointHom houghtonS*P)^d) (Concrete.Ray.one,1)=(Concrete.Ray.one,max i j) := by
    rw [Equiv.Perm.mul_apply,spPoint_power_one,pPoint_pow_one]
    have : d+1+l=max i j := by dsimp [d,l]; omega
    rw [this]
  calc
    _=(P^l*(S*P)^d)*Equiv.swap (Concrete.Ray.one,0) (Concrete.Ray.one,1)*(P^l*(S*P)^d)⁻¹ := by
      rw [hword]
      exact congrArg (fun z => (P^l*(S*P)^d)*z*(P^l*(S*P)^d)⁻¹) point_s_swap
    _=Equiv.swap ((P^l*(S*P)^d) (Concrete.Ray.one,0))
        ((P^l*(S*P)^d) (Concrete.Ray.one,1)) :=
      Equiv.symm_trans_swap_trans (Concrete.Ray.one,0) (Concrete.Ray.one,1) (P^l*(S*P)^d)
    _=Equiv.swap (Concrete.Ray.one,i) (Concrete.Ray.one,j) := by
      rw [h0,h1]
      by_cases hij : i≤j
      · simp only [l,min_eq_left hij,max_eq_right hij]
      · rw [show l=j by dsimp [l]; omega,show max i j=i by omega,Equiv.swap_comm]

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.mk_repeated_word
#print axioms Blueprint.PairProof.point_s_swap
#print axioms Blueprint.PairProof.mk_repeated_letter
#print axioms Blueprint.PairProof.spPoint_power_zero
#print axioms Blueprint.PairProof.spPoint_power_one
#print axioms Blueprint.PairProof.omega_permutation
