import Companion.ProjectionProducts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Module

namespace Companion.Analytic
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 300000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A self-adjoint involution of the real Hilbert space. A negative sign is
absorbed into the operator, so this includes both signs of a twirl. -/
structure Reflection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  op : E →ₗ[ℝ] E
  square : ∀ v, op (op v)=v
  selfAdjoint : ∀ v w, inner ℝ (op v) w=inner ℝ v (op w)

theorem Reflection.norm_sq (p : Reflection E) (v : E) : ‖p.op v‖^2=‖v‖^2 := by
  rw [← real_inner_self_eq_norm_sq, p.selfAdjoint,p.square,real_inner_self_eq_norm_sq]

theorem Reflection.norm (p : Reflection E) (v : E) : ‖p.op v‖=‖v‖ := by
  nlinarith [p.norm_sq v,norm_nonneg v,norm_nonneg (p.op v)]

def Reflection.projection (p : Reflection E) : OrthogonalMap E where
  op := (1/2:ℝ) • (LinearMap.id+p.op)
  idempotent v := by
    change (1/2:ℝ) • ((1/2:ℝ) • (v+p.op v)+p.op ((1/2:ℝ) • (v+p.op v)))=(1/2:ℝ) • (v+p.op v)
    rw [map_smul,map_add,p.square]
    module
  selfAdjoint v w := by
    change inner ℝ ((1/2:ℝ) • (v+p.op v)) w=inner ℝ v ((1/2:ℝ) • (w+p.op w))
    simp only [real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right,p.selfAdjoint]

def Reflection.neg (p : Reflection E) : Reflection E where
  op := -p.op
  square v := by simp [p.square]
  selfAdjoint v w := by simp [p.selfAdjoint]

theorem sum_cube_succ {A : Type*} [AddCommMonoid A] {n : Nat}
    (f : (Fin (n+1) → Bool) → A) :
    (∑ g, f g)=∑ b : Bool, ∑ g : Fin n → Bool, f (Fin.cons b g) := by
  calc
    _=∑ x : Bool × (Fin n → Bool), f (Fin.cons x.1 x.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) _ _ (fun _ => rfl)).symm
    _=_ := Fintype.sum_prod_type _

def reflectionWord : (ps : List (Reflection E)) → (Fin ps.length → Bool) → E →ₗ[ℝ] E
  | [],_ => LinearMap.id
  | p::ps,g => (reflectionWord ps (Fin.tail g)).comp (if g 0 then p.op else LinearMap.id)

theorem reflectionWord_norm (ps : List (Reflection E)) (g : Fin ps.length → Bool) (v : E) :
    ‖reflectionWord ps g v‖=‖v‖ := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih =>
    simp only [reflectionWord,LinearMap.comp_apply]
    rw [ih]
    split <;> simp [Reflection.norm]

theorem projectionRun_add (ps : List (OrthogonalMap E)) (v w : E) :
    projectionRun ps (v+w)=projectionRun ps v+projectionRun ps w := by
  induction ps generalizing v w with
  | nil => rfl
  | cons p ps ih => simp only [projectionRun,map_add,ih]

theorem projectionRun_smul (ps : List (OrthogonalMap E)) (a : ℝ) (v : E) :
    projectionRun ps (a • v)=a • projectionRun ps v := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih => simp only [projectionRun,map_smul,ih]

/-- Exact average of all Boolean choices of the reflections. No pairwise
commutativity of the reflections is assumed. -/
theorem reflectionWord_sum (ps : List (Reflection E)) (v : E) :
    (∑ g : Fin ps.length → Bool, reflectionWord ps g v)=
      (2:ℝ)^ps.length • projectionRun (ps.map Reflection.projection) v := by
  induction ps generalizing v with
  | nil => simp [reflectionWord,projectionRun]
  | cons p ps ih =>
    change (∑ g : Fin (ps.length+1) → Bool, reflectionWord (p::ps) g v)=_
    rw [sum_cube_succ]
    simp only [Fintype.sum_bool,reflectionWord,Fin.cons_zero,Fin.tail_cons,
      Bool.false_eq_true,↓reduceIte,LinearMap.comp_apply,LinearMap.id_apply]
    rw [ih,ih]
    simp only [List.map_cons,projectionRun,Reflection.projection,LinearMap.smul_apply,
      LinearMap.add_apply,LinearMap.id_apply,projectionRun_smul,projectionRun_add,List.length_cons,pow_succ]
    module

theorem reflectionWord_distance_sum (ps : List (Reflection E)) (v : E) :
    (∑ g : Fin ps.length → Bool, ‖reflectionWord ps g v-v‖^2)=
      (2:ℝ)^ps.length*(2*‖v‖^2-2*inner ℝ v (projectionRun (ps.map Reflection.projection) v)) := by
  simp_rw [norm_sub_sq_real,reflectionWord_norm]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← sum_inner,
    reflectionWord_sum,real_inner_smul_left,real_inner_comm (projectionRun _ v) v]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem reflection_projection_loss (p : Reflection E) (v : E) :
    4*‖v-p.projection.op v‖^2=‖v-p.op v‖^2 := by
  have he : v-p.projection.op v=(1/2:ℝ) • (v-p.op v) := by
    change v-(1/2:ℝ) • (v+p.op v)=(1/2:ℝ) • (v-p.op v)
    module
  rw [he,norm_smul]
  norm_num
  ring

/-- The two-sided twirl bound in a real Hilbert space, with the exact sum
of squared errors and no dependence on the number of reflections. -/
theorem twirl_bound (ps : List (Reflection E)) (v : E) :
    (∑ g : Fin ps.length → Bool, ‖reflectionWord ps g v-v‖^2)/(2:ℝ)^ps.length≤
      (ps.map (fun p => ‖v-p.op v‖^2)).sum := by
  rw [reflectionWord_distance_sum,mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))]
  have hl : 4*projectionLoss (ps.map Reflection.projection) v=
      (ps.map (fun p => ‖v-p.op v‖^2)).sum := by
    simp only [projectionLoss,List.map_map,Function.comp_def]
    induction ps with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons,List.sum_cons,mul_add,reflection_projection_loss,ih]
  have hp := projection_product_bound (ps.map Reflection.projection) v
  linarith

end
end Companion.Analytic
