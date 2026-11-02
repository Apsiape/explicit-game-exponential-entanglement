import Companion.BranchDisturbance

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem sum_cube_snoc {A : Type*} [AddCommMonoid A] {n : Nat}
    (f : (Fin (n+1) → Bool) → A) :
    (∑ a, f a)=∑ b : Bool, ∑ a : Fin n → Bool, f (Fin.snoc a b) := by
  calc
    _=∑ t : Bool × (Fin n → Bool), f (Fin.snoc t.2 t.1) :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)) _ _ (fun _ => rfl)).symm
    _=_ := Fintype.sum_prod_type _

theorem familyHS_cube_snoc {d n : Nat} (F : (Fin (n+1) → Bool) → Mat d) :
    familyHS F=familyHS (fun t : Bool × (Fin n → Bool) => F (Fin.snoc t.2 t.1)) := by
  apply (sq_eq_sq₀ (familyHS_nonneg _) (familyHS_nonneg _)).mp
  rw [familyHS_sq,familyHS_sq,sum_cube_snoc,Fintype.sum_prod_type]

theorem jointProjection_snoc {d n : Nat} (Q : Fin (n+1) → Mat d) (a : Fin (n+1) → Bool) :
    CountProof.jointProjection (n+1) Q a=signProjection (Q (Fin.last n)) (a (Fin.last n))*
      CountProof.jointProjection n (Fin.init Q) (Fin.init a) := by
  rw [jointProjection_reverseProd,jointProjection_reverseProd,List.ofFn_succ_last]
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.prod_append,
    List.prod_cons,List.prod_nil,Matrix.mul_one,Matrix.one_mul]
  rfl

theorem sequential_disturbance_uniform {d : Nat} (n : Nat) (Q : Fin n → Mat d)
    (hQ : ∀ j, IsInvolution (Q j)) (C eta : Mat d) (hC : IsInvolution C) (c k : ℝ)
    (hc : ∀ j, hsNorm (comm (Q j) eta)≤c) (hk : ∀ j, hsNorm (comm C (Q j)*eta)≤k) :
    familyHS (fun a => comm C (CountProof.jointProjection n Q a)*eta)≤
      (n:ℝ)*k/Real.sqrt 2+(n:ℝ)*((n:ℝ)-1)*c/2 := by
  induction n with
  | zero => simp [CountProof.jointProjection,comm,familyHS,stackMatrices,hsNorm,hsSquared]
  | succ n ih =>
    have hi := ih (Fin.init Q) (fun j => hQ j.castSucc)
      (fun j => hc j.castSucc) (fun j => hk j.castSucc)
    have hd := sequential_branch_commutator_uniform n (Fin.init Q) (fun j => hQ j.castSucc) eta c
      (fun j => hc j.castSucc)
    rw [familyHS_cube_snoc]
    simp_rw [jointProjection_snoc]
    simp only [Fin.snoc_last,Fin.init_snoc]
    have h := disturbance_step (CountProof.jointProjection n (Fin.init Q))
      (jointProjection_coComplete n _ (fun j => hQ j.castSucc)) C (Q (Fin.last n)) eta hC (hQ _)
    have hr : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hb : hsNorm (comm C (Q (Fin.last n))*eta)+
        2*familyHS (fun a => comm (CountProof.jointProjection n (Fin.init Q) a) eta)≤k+2*((n:ℝ)*c/Real.sqrt 2) := by
      linarith [hk (Fin.last n)]
    calc
      _≤(n:ℝ)*k/Real.sqrt 2+(n:ℝ)*((n:ℝ)-1)*c/2+
          (k+2*((n:ℝ)*c/Real.sqrt 2))/Real.sqrt 2 :=
        h.trans (add_le_add hi (div_le_div_of_nonneg_right hb hr.le))
      _=_ := by
        push_cast
        field_simp
        ring_nf
        simp only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
        ring

end
end Companion.Analytic.ReturnProof
