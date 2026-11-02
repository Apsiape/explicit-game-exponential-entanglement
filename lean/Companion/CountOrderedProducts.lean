import Companion.WeightedTwirl
import Companion.CountPauliEmbedding

namespace Companion.Analytic.CountProof
noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 500000

theorem orderedProduct_split {G : Type*} [Monoid G] (n : Nat) (U : Fin n → G) (i : Fin n) :
    (List.ofFn U).prod=(List.ofFn (fun j => if j < i then U j else 1)).prod*U i*
      (List.ofFn (fun j => if i < j then U j else 1)).prod := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [List.ofFn_succ]
    · simpa [List.ofFn_succ,Fin.succ_pos,Fin.succ_lt_succ_iff,mul_assoc] using
        congrArg (fun v => U 0*v) (ih (fun j => U j.succ) k)

def maskedZ {n d : Nat} (Z : Fin n → Mat d) (p : Fin n → Prop) [DecidablePred p] (j : Fin n) : Mat d :=
  if p j then Z j else 1

theorem maskedZ_involution {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (p : Fin n → Prop) [DecidablePred p] (j : Fin n) : IsInvolution (maskedZ Z p j) := by
  by_cases h : p j
  · simpa [maskedZ,h] using hZ j
  · simp [maskedZ,h,IsInvolution]

theorem orderedZ_mask_flip {n d : Nat} (Z : Fin n → Mat d) (p : Fin n → Prop) [DecidablePred p]
    (g : Fin n → Bool) (i : Fin n) (hi : ¬p i) :
    orderedZ (maskedZ Z p) (flip g i)=orderedZ (maskedZ Z p) g := by
  unfold orderedZ
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  by_cases h : j=i
  · subst j; simp [maskedZ,hi]
  · simp [flip,Function.update_of_ne h]

theorem orderedZ_split {n d : Nat} (Z : Fin n → Mat d) (g : Fin n → Bool) (i : Fin n) :
    orderedZ Z g=orderedZ (maskedZ Z (fun j => j < i)) g*(if g i then Z i else 1)*
      orderedZ (maskedZ Z (fun j => i < j)) g := by
  have h := orderedProduct_split n (fun j => if g j then Z j else 1) i
  have hp (j : Fin n) : (if j < i then (if g j then Z j else 1) else 1)=
      (if g j then maskedZ Z (fun j => j < i) j else 1) := by
    cases hg : g j <;> simp [maskedZ,hg]
  have hq (j : Fin n) : (if i < j then (if g j then Z j else 1) else 1)=
      (if g j then maskedZ Z (fun j => i < j) j else 1) := by
    cases hg : g j <;> simp [maskedZ,hg]
  simpa only [hp,hq,orderedZ] using h

theorem involution_unitary {d : Nat} (Y : Mat d) (hY : IsInvolution Y) : IsUnitary Y := by
  constructor <;> rw [hY.1,hY.2]

theorem a_pointwise_norm {n d : Nat} (Z : Fin n → Mat d) (hZ : ∀ i, IsInvolution (Z i))
    (g : Fin n → Bool) (i : Fin n) (xi : Mat d) :
    hsNorm ((orderedZ Z (flip g i)-orderedZ Z g*Z i)*xi)=
      hsNorm (((orderedZ (maskedZ Z (fun j => i < j)) g).conjTranspose*Z i*
        orderedZ (maskedZ Z (fun j => i < j)) g-Z i)*xi) := by
  let L := orderedZ (maskedZ Z (fun j => j < i)) g
  let R := orderedZ (maskedZ Z (fun j => i < j)) g
  let A : Mat d := if g i then Z i else 1
  have hpre := orderedZ_mask_flip Z (fun j => j < i) g i (lt_irrefl i)
  have hpost := orderedZ_mask_flip Z (fun j => i < j) g i (lt_irrefl i)
  have hflip : (if flip g i i then Z i else 1)=A*Z i := by
    cases hg : g i <;> simp [A,flip,hg,(hZ i).2]
  have he : (orderedZ Z (flip g i)-orderedZ Z g*Z i)*xi=(L*A)*((Z i*R-R*Z i)*xi) := by
    rw [orderedZ_split Z (flip g i) i,orderedZ_split Z g i,hpre,hpost,hflip]
    simp only [L,R,A,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_assoc]
  have hL := orderedZ_unitary (maskedZ Z (fun j => j < i)) (maskedZ_involution Z hZ _) g
  have hR := orderedZ_unitary (maskedZ Z (fun j => i < j)) (maskedZ_involution Z hZ _) g
  have hA : A.conjTranspose*A=1 := by
    cases hg : g i <;> simp [A,hg,(hZ i).1,(hZ i).2]
  have hLA : (L*A).conjTranspose*(L*A)=1 := by
    calc
      _=A.conjTranspose*((L.conjTranspose*L)*A) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _=1 := by rw [hL.1,Matrix.one_mul,hA]
  rw [he,hsNorm_unitary_left _ _ hLA]
  have hc : R.conjTranspose*(Z i*R-R*Z i)=R.conjTranspose*Z i*R-Z i := by
    calc
      _=R.conjTranspose*Z i*R-(R.conjTranspose*R)*Z i := by
        simp only [Matrix.mul_sub,Matrix.mul_assoc]
      _=_ := by rw [hR.1,Matrix.one_mul]
  calc
    _=hsNorm (R.conjTranspose*((Z i*R-R*Z i)*xi)) :=
      (hsNorm_unitary_left R.conjTranspose _ (by simpa only [Matrix.conjTranspose_conjTranspose] using hR.2)).symm
    _=_ := by rw [← Matrix.mul_assoc,hc]

theorem intertwining_norm {d : Nat} (F Y xi : Mat d) (c : ℂ) (hF : IsUnitary F) :
    hsNorm ((c • (Y*F)-F*Y)*xi)=hsNorm ((c • (F.conjTranspose*Y*F)-Y)*xi) := by
  have hh : F*(F.conjTranspose*Y*F)=Y*F := by
    calc
      _=(F*F.conjTranspose)*(Y*F) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hF.2,Matrix.one_mul]
  have he : (c • (Y*F)-F*Y)*xi=F*((c • (F.conjTranspose*Y*F)-Y)*xi) := by
    rw [← Matrix.mul_assoc F _ xi,Matrix.mul_sub,Matrix.mul_smul,hh]
  rw [he,hsNorm_unitary_left F _ hF.1]

theorem signedCoefficient_single {n : Nat} (g : Fin n → Bool) (i : Fin n) :
    signedCoefficient (fun j => decide (j=i)) g=(if g i then (-1:ℂ) else 1) := by
  unfold signedCoefficient
  rw [List.prod_ofFn]
  have h := Finset.prod_eq_single (s:=Finset.univ) (f:=fun j => if g j && decide (j=i) then (-1:ℂ) else 1) i
    (fun j hj hji => by simp [hji]) (by simp)
  simpa using h

end
end Companion.Analytic.CountProof

