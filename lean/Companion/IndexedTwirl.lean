import Companion.MatrixTwirl
import Companion.CountEmbedding
import Mathlib.Algebra.BigOperators.Fin

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def indexedWord : (n : Nat) → (Fin n → Reflection E) → (Fin n → Bool) → E →ₗ[ℝ] E
  | 0,_,_ => LinearMap.id
  | n+1,T,g => (indexedWord n (Fin.tail T) (Fin.tail g)).comp (if g 0 then (T 0).op else LinearMap.id)

theorem indexedWord_norm (n : Nat) (T : Fin n → Reflection E) (g : Fin n → Bool) (v : E) :
    ‖indexedWord n T g v‖=‖v‖ := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [indexedWord,LinearMap.comp_apply]
    rw [ih]
    split <;> simp [Reflection.norm]

theorem indexedWord_sum (n : Nat) (T : Fin n → Reflection E) (v : E) :
    (∑ g : Fin n → Bool, indexedWord n T g v)=
      (2:ℝ)^n • projectionRun (List.ofFn (fun i => (T i).projection)) v := by
  induction n generalizing v with
  | zero => simp [indexedWord,projectionRun]
  | succ n ih =>
    rw [sum_cube_succ]
    simp only [Fintype.sum_bool,indexedWord,Fin.cons_zero,Fin.tail_cons,
      Bool.false_eq_true,↓reduceIte,LinearMap.comp_apply,LinearMap.id_apply]
    rw [ih,ih]
    simp only [List.ofFn_succ,projectionRun,Reflection.projection,LinearMap.smul_apply,
      LinearMap.add_apply,LinearMap.id_apply,projectionRun_smul,projectionRun_add,pow_succ,Fin.tail_def]
    module

theorem indexed_twirl_bound (n : Nat) (T : Fin n → Reflection E) (v : E) :
    (∑ g : Fin n → Bool, ‖indexedWord n T g v-v‖^2)/(2:ℝ)^n≤
      ∑ i, ‖v-(T i).op v‖^2 := by
  have he : (∑ g : Fin n → Bool, ‖indexedWord n T g v-v‖^2)=
      (2:ℝ)^n*(2*‖v‖^2-2*inner ℝ v (projectionRun (List.ofFn (fun i => (T i).projection)) v)) := by
    simp_rw [norm_sub_sq_real,indexedWord_norm]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← sum_inner,
      indexedWord_sum,real_inner_smul_left,real_inner_comm (projectionRun _ v) v]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [he,mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))]
  have hp := projection_product_bound (List.ofFn (fun i => (T i).projection)) v
  have hl : 4*projectionLoss (List.ofFn (fun i => (T i).projection)) v=∑ i, ‖v-(T i).op v‖^2 := by
    simp only [projectionLoss,List.map_ofFn,List.sum_ofFn,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => reflection_projection_loss (T i) v)
  linarith

def signedCoefficient {n : Nat} (sig g : Fin n → Bool) : ℂ :=
  (List.ofFn (fun i => if g i && sig i then (-1:ℂ) else 1)).prod

theorem orderedZ_succ {n d : Nat} (Z : Fin (n+1) → Mat d) (g : Fin (n+1) → Bool) :
    orderedZ Z g=(if g 0 then Z 0 else 1)*orderedZ (Fin.tail Z) (Fin.tail g) := by
  simp only [orderedZ,List.ofFn_succ,List.prod_cons,Fin.tail_def]
  rfl

theorem signedCoefficient_succ {n : Nat} (sig g : Fin (n+1) → Bool) :
    signedCoefficient sig g=(if g 0 && sig 0 then (-1:ℂ) else 1)*
      signedCoefficient (Fin.tail sig) (Fin.tail g) := by
  simp only [signedCoefficient,List.ofFn_succ,List.prod_cons,Fin.tail_def]
  rfl

def signedReflection {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (sig : Fin n → Bool) (i : Fin n) : Reflection (HSSpace d) :=
  (SignedInvolution.mk (Z i) (hZ i) (sig i)).reflection

theorem indexedWord_matrix {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (sig g : Fin n → Bool) (v : Mat d) :
    indexedWord n (signedReflection Z hZ sig) g (hsVector v)=
      hsVector (signedCoefficient sig g • ((orderedZ Z g).conjTranspose*v*orderedZ Z g)) := by
  induction n generalizing v with
  | zero => simp [indexedWord,orderedZ,signedCoefficient,hsVector]
  | succ n ih =>
    simp only [indexedWord,LinearMap.comp_apply]
    change indexedWord n (signedReflection (fun i => Z i.succ) (fun i => hZ i.succ) (fun i => sig i.succ))
      (fun i => g i.succ) ((if g 0 then (signedReflection Z hZ sig 0).op else LinearMap.id) (hsVector v))=_
    cases hg : g 0 <;> cases hs : sig 0 <;>
      simp [signedReflection,SignedInvolution.reflection,hg,hs,matrixReflection,
        Reflection.neg,LinearMap.neg_apply,LinearMap.id_apply,conjugationOp_apply,← hsVector_neg] <;>
      rw [ih] <;>
      simp [signedCoefficient_succ,orderedZ_succ,hg,hs,(hZ 0).1,
        Matrix.conjTranspose_mul,Matrix.mul_assoc,Matrix.mul_neg,Matrix.neg_mul,
        Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm,Fin.tail_def] <;> rfl

theorem signed_twirl_bound {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (sig : Fin n → Bool) (v : Mat d) :
    (∑ g : Fin n → Bool,
      hsNorm (signedCoefficient sig g • ((orderedZ Z g).conjTranspose*v*orderedZ Z g)-v)^2)/(2:ℝ)^n≤
      ∑ i, hsNorm (if sig i then anti (Z i) v else comm (Z i) v)^2 := by
  have h := indexed_twirl_bound n (signedReflection Z hZ sig) (hsVector v)
  simp_rw [indexedWord_matrix,← hsVector_sub,hsVector_norm] at h
  have he (i : Fin n) : ‖hsVector v-(signedReflection Z hZ sig i).op (hsVector v)‖=
      hsNorm (if sig i then anti (Z i) v else comm (Z i) v) :=
    SignedInvolution.reflection_error ⟨Z i,hZ i,sig i⟩ v
  simpa only [he] using h

end
end Companion.Analytic.CountProof
