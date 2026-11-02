import Companion.HilbertSchmidt
import Companion.Soundness
set_option maxHeartbeats 500000

namespace Companion
noncomputable section

structure InvariantLength (G : Type*) [Group G] where
  value : G → ℝ
  nonneg : ∀ g, 0≤value g
  one : value 1=0
  mul_le : ∀ g h, value (g*h)≤value g+value h
  inv : ∀ g, value g⁻¹=value g
  conjugate : ∀ g h, value (g*h*g⁻¹)=value h

theorem mk_expandWith (rfn : RelKey → Option Word) (fs : List Factor) :
    FreeGroup.mk (expandWith rfn fs)=(fs.map (fun f => FreeGroup.mk (factorWordWith rfn f))).prod := by
  induction fs with
  | nil => simp [expandWith,← FreeGroup.one_eq_mk]
  | cons f fs ih => simp only [expandWith,List.map_cons,List.flatten_cons,← FreeGroup.mul_mk,
      List.prod_cons] at *; rw [ih]

/-- A kernel-checked area witness controls every conjugation-invariant
subadditive length. The matrix instance is constructed below. -/
theorem HasAreaWith.length_bound {G : Type*} [Group G] (L : InvariantLength G)
    {rfn : RelKey → Option Word} {w : Word} {bound : Nat} (ha : HasAreaWith rfn w bound)
    (phi : FreeGroup Nat →* G) (eps : ℝ) (heps : 0≤eps)
    (hr : ∀ k r, rfn k=some r → L.value (phi (FreeGroup.mk r))≤eps) :
    L.value (phi (FreeGroup.mk w))≤bound*eps := by
  obtain ⟨fs,hb,hvalid,he⟩ := ha
  have hf (f : Factor) (hmem : f ∈ fs) : L.value (phi (FreeGroup.mk (factorWordWith rfn f)))≤eps := by
    cases hk : rfn f.key with
    | none => have := hvalid f hmem; simp [hk] at this
    | some r =>
      have hh := hr f.key r hk
      cases hp : f.positive <;>
        simpa only [factorWordWith,hk,Option.getD_some,hp,Bool.false_eq_true,↓reduceIte,
          ← FreeGroup.mul_mk,← FreeGroup.inv_mk,map_mul,map_inv,L.conjugate,L.inv] using hh
  have hp : ∀ xs : List Factor,
      (∀ f ∈ xs, L.value (phi (FreeGroup.mk (factorWordWith rfn f)))≤eps) →
      L.value (phi ((xs.map (fun f => FreeGroup.mk (factorWordWith rfn f))).prod))≤xs.length*eps := by
    intro xs
    induction xs with
    | nil => intro _; simp [L.one]
    | cons f xs ih =>
      intro hxs
      simp only [List.map_cons,List.prod_cons,map_mul,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      exact (L.mul_le _ _).trans (add_le_add (hxs f (List.mem_cons_self ..))
        (ih (fun x hx => hxs x (List.mem_cons_of_mem f hx)))) |>.trans (le_of_eq (add_comm _ _))
  rw [← he,mk_expandWith]
  exact (hp fs hf).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) heps)

namespace Analytic
open scoped Matrix.Norms.Frobenius

def normalizedHS {d : Nat} (A : Mat d) : ℝ := (Real.sqrt (d:ℝ))⁻¹*hsNorm A

def unitaryHSLength (d : Nat) : InvariantLength (Matrix.unitaryGroup (Fin d) ℂ) where
  value U := normalizedHS ((U : Mat d)-1)
  nonneg U := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (hsNorm_nonneg _)
  one := by simp [normalizedHS,hsNorm_eq_frobenius]
  mul_le U V := by
    have he : ((U*V : Matrix.unitaryGroup (Fin d) ℂ) : Mat d)-1 =
        (U:Mat d)*((V:Mat d)-1)+((U:Mat d)-1) := by
      simp only [Submonoid.coe_mul,Matrix.mul_sub,Matrix.mul_one,sub_add_sub_cancel]
    change (Real.sqrt (d:ℝ))⁻¹*hsNorm _ ≤ _
    rw [he]
    have ht := hsNorm_add_le ((U:Mat d)*((V:Mat d)-1)) ((U:Mat d)-1)
    rw [hsNorm_unitary_left (U:Mat d) _ U.property.1] at ht
    unfold normalizedHS
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (ht.trans (le_of_eq (add_comm _ _)))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  inv U := by
    have he : ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : Mat d)-1 =
        ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : Mat d)*(1-(U:Mat d)) := by
      change (U:Analytic.Mat d).conjTranspose-1 =
        (U:Analytic.Mat d).conjTranspose*(1-(U:Analytic.Mat d))
      have hu : (U:Analytic.Mat d).conjTranspose*(U:Analytic.Mat d)=1 := U.property.1
      rw [Matrix.mul_sub,Matrix.mul_one,hu]
    unfold normalizedHS
    rw [he,hsNorm_unitary_left _ _ (U⁻¹).property.1]
    congr 1
    simp only [hsNorm_eq_frobenius,norm_sub_rev]
  conjugate U V := by
    have he : ((U*V*U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : Mat d)-1 =
        (U:Mat d)*((V:Mat d)-1)*((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ):Mat d) := by
      change (U:Analytic.Mat d)*(V:Analytic.Mat d)*(U:Analytic.Mat d).conjTranspose-1 =
        (U:Analytic.Mat d)*((V:Analytic.Mat d)-1)*(U:Analytic.Mat d).conjTranspose
      have hu : (U:Analytic.Mat d)*(U:Analytic.Mat d).conjTranspose=1 := U.property.2
      rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hu]
    unfold normalizedHS
    rw [he,hsNorm_unitary_right _ _ (U⁻¹).property.2,hsNorm_unitary_left _ _ U.property.1]

end Analytic
end
end Companion
