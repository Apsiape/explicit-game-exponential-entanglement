import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

namespace Companion.Analytic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The usual algebraic definition of an orthogonal projection. -/
structure OrthogonalMap (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  op : E →ₗ[ℝ] E
  idempotent : ∀ v, op (op v)=op v
  selfAdjoint : ∀ v w, inner ℝ (op v) w=inner ℝ v (op w)

def projectionRun (ps : List (OrthogonalMap E)) (v : E) : E :=
  match ps with
  | [] => v
  | p::ps => projectionRun ps (p.op v)

def projectionLoss (ps : List (OrthogonalMap E)) (y : E) : ℝ :=
  (ps.map (fun p => ‖y-p.op y‖^2)).sum

theorem projection_energy (p : OrthogonalMap E) (v : E) :
    ‖v-p.op v‖^2=‖v‖^2-‖p.op v‖^2 := by
  have he : inner ℝ v (p.op v)=inner ℝ (p.op v) (p.op v) := by
    simpa only [p.idempotent] using (p.selfAdjoint v (p.op v)).symm
  rw [norm_sub_sq_real,he,real_inner_self_eq_norm_sq]
  ring

private theorem projection_inner (p : OrthogonalMap E) (y v : E) :
    inner ℝ y (v-p.op v)=inner ℝ (y-p.op y) (v-p.op v) := by
  have he : inner ℝ (p.op y) (v-p.op v)=0 := by
    rw [p.selfAdjoint,map_sub,p.idempotent,sub_self,inner_zero_right]
  rw [inner_sub_left,he,sub_zero]

private theorem young_inner (a b : E) : inner ℝ a b≤‖a‖^2+‖b‖^2/4 := by
  have h := real_inner_le_norm a b
  nlinarith [sq_nonneg (‖a‖-‖b‖/2)]

theorem projection_run_estimate (ps : List (OrthogonalMap E)) (y v : E) :
    inner ℝ y (v-projectionRun ps v)≤
      projectionLoss ps y+(‖v‖^2-‖projectionRun ps v‖^2)/4 := by
  induction ps generalizing v with
  | nil => simp [projectionRun,projectionLoss]
  | cons p ps ih =>
    have hi := ih (p.op v)
    have hh := young_inner (y-p.op y) (v-p.op v)
    rw [← projection_inner] at hh
    rw [projection_energy p v] at hh
    have he : v-projectionRun ps (p.op v)=
        (v-p.op v)+(p.op v-projectionRun ps (p.op v)) := by abel
    simp only [projectionRun,projectionLoss,List.map_cons,List.sum_cons] at *
    rw [he,inner_add_right]
    linarith

/-- Lemma 3.7 (projection products), in any real Hilbert space. Applying it
to the real part of a complex Hilbert inner product gives the paper's form. -/
theorem projection_product_bound (ps : List (OrthogonalMap E)) (y : E) :
    ‖y‖^2-inner ℝ y (projectionRun ps y)≤2*projectionLoss ps y := by
  have h := projection_run_estimate ps y y
  have hnorm := norm_sub_sq_real y (projectionRun ps y)
  have hn := sq_nonneg ‖y-projectionRun ps y‖
  rw [inner_sub_right,real_inner_self_eq_norm_sq] at h
  nlinarith

end
end Companion.Analytic
