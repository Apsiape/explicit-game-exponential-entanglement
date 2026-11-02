import Blueprint.AHash

namespace Blueprint.AHash
noncomputable section
open Companion Concrete

def boxRay : Fin 3 ≃ Ray where
  toFun j := if j=0 then .one else if j=1 then .two else .three
  invFun r := match r with | .one => 0 | .two => 1 | .three => 2
  left_inv j := by fin_cases j <;> decide
  right_inv r := by cases r <;> decide

abbrev BoxIndex (r : Nat) := Fin 3 × Fin r
abbrev BoxVector (r : Nat) := BoxIndex r → Bool

def boxPoint {r : Nat} (i : BoxIndex r) : Point := (boxRay i.1,i.2.val)

theorem boxPoint_injective (r : Nat) : Function.Injective (boxPoint (r:=r)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  exact Prod.ext (boxRay.injective (congrArg Prod.fst h))
    (Fin.ext (congrArg Prod.snd h))

def boxEncode {r : Nat} (v : BoxVector r) : Config :=
  (Finset.univ.filter (fun i => v i=true)).image boxPoint

def boxDecode (r : Nat) (v : Config) : BoxVector r := fun i => bit v (boxPoint i)

def boxCoord (r : Nat) (y : Point) (hy : y.2<r) : BoxIndex r :=
  (boxRay.symm y.1,⟨y.2,hy⟩)

theorem boxPoint_coord (r : Nat) (y : Point) (hy : y.2<r) :
    boxPoint (boxCoord r y hy)=y := by simp [boxPoint,boxCoord]

theorem boxEncode_bit {r : Nat} (v : BoxVector r) (i : BoxIndex r) :
    bit (boxEncode v) (boxPoint i)=v i := by
  simp only [bit,boxEncode,Finset.mem_image]
  have hh : (∃ a, (a∈Finset.univ.filter (fun i => v i=true)) ∧ boxPoint a=boxPoint i) ↔ v i=true := by
    simp only [(boxPoint_injective r).eq_iff,exists_eq_right,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [hh]
  cases v i <;> rfl

theorem boxEncode_outside {r : Nat} (v : BoxVector r) (y : Point) (hy : r≤y.2) :
    bit (boxEncode v) y=false := by
  have hn : y∉boxEncode v := by
    intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    have hh := congrArg Prod.snd hi
    change i.2.val=y.2 at hh
    have := i.2.isLt
    omega
  simp [bit,hn]

theorem boxDecode_encode {r : Nat} (v : BoxVector r) : boxDecode r (boxEncode v)=v := by
  funext i
  exact boxEncode_bit v i

def BoxSupported (r : Nat) (v : Config) : Prop := ∀ y, r≤y.2 → bit v y=false

theorem boxEncode_supported {r : Nat} (v : BoxVector r) : BoxSupported r (boxEncode v) :=
  boxEncode_outside v

theorem boxEncode_decode (r : Nat) (v : Config) (hv : BoxSupported r v) :
    boxEncode (boxDecode r v)=v := by
  apply Finset.ext
  intro y
  have hh : bit (boxEncode (boxDecode r v)) y=bit v y := by
    by_cases hy : y.2<r
    · rw [←boxPoint_coord r y hy,boxEncode_bit]
      rfl
    · rw [boxEncode_outside _ y (by omega),hv y (by omega)]
  simpa only [bit,decide_eq_decide] using hh

theorem hostEval_append (u v : List HostLetter) : hostEval (u++v)=hostEval u*hostEval v := by
  induction u with
  | nil => simp [hostEval]
  | cons a u ih => simp only [List.cons_append,hostEval,ih,mul_assoc]

theorem hostGenerator_inverse (a : HostLetter) : hostGenerator (inverseHost a)=(hostGenerator a)⁻¹ := by
  cases a <;> rfl

theorem hostEval_inverse (w : List HostLetter) : hostEval (inverseHostWord w)=(hostEval w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [inverseHostWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      hostEval_append,hostEval,hostGenerator_inverse,mul_one,mul_inv_rev] at *
    exact congrArg (fun e => e*(hostGenerator a)⁻¹) ih

def BoxFixed (r : Nat) (w : List HostLetter) : Prop :=
  ∀ v y, r≤y.2 → bit (hostEval w v) y=bit v y

theorem boxFixed_supported {r : Nat} {w : List HostLetter} (hw : BoxFixed r w)
    (v : Config) (hv : BoxSupported r v) : BoxSupported r (hostEval w v) := by
  intro y hy
  rw [hw v y hy,hv y hy]

theorem boxFixed_inverse {r : Nat} {w : List HostLetter} (hw : BoxFixed r w) :
    BoxFixed r (inverseHostWord w) := by
  intro v y hy
  rw [hostEval_inverse]
  have hh := hw ((hostEval w).symm v) y hy
  simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm

def boxHostMap (r : Nat) (w : List HostLetter) (v : BoxVector r) : BoxVector r :=
  boxDecode r (hostEval w (boxEncode v))

theorem boxHostMap_encode {r : Nat} {w : List HostLetter} (hw : BoxFixed r w) (v : BoxVector r) :
    boxEncode (boxHostMap r w v)=hostEval w (boxEncode v) :=
  boxEncode_decode r _ (boxFixed_supported hw _ (boxEncode_supported v))

def boxHostPerm (r : Nat) (w : List HostLetter) (hw : BoxFixed r w) : Equiv.Perm (BoxVector r) where
  toFun := boxHostMap r w
  invFun := boxHostMap r (inverseHostWord w)
  left_inv v := by
    change boxDecode r (hostEval (inverseHostWord w) (boxEncode (boxHostMap r w v)))=v
    rw [boxHostMap_encode hw,hostEval_inverse]
    simpa only [Equiv.Perm.inv_def,Equiv.symm_apply_apply] using boxDecode_encode v
  right_inv v := by
    change boxDecode r (hostEval w (boxEncode (boxHostMap r (inverseHostWord w) v)))=v
    rw [boxHostMap_encode (boxFixed_inverse hw),hostEval_inverse]
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using boxDecode_encode v

theorem boxEncode_add_bit {r : Nat} (v u : BoxVector r) (y : Point) :
    bit (boxEncode (v+u)) y=bit (boxEncode v) y+bit (boxEncode u) y := by
  by_cases hy : y.2<r
  · rw [←boxPoint_coord r y hy,boxEncode_bit,boxEncode_bit,boxEncode_bit]
    rfl
  · simp only [boxEncode_outside _ y (by omega : r≤y.2)]
    rfl

theorem boxEncode_zero_bit (r : Nat) (y : Point) : bit (boxEncode (0:BoxVector r)) y=false := by
  by_cases hy : y.2<r
  · rw [←boxPoint_coord r y hy,boxEncode_bit]
    rfl
  · exact boxEncode_outside _ y (by omega)

theorem parity_add (f g : Point → Bool) (ys : List Point) :
    parity (f+g) ys=parity f ys+parity g ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [parity,ih,Pi.add_apply,←Bool.add_eq_xor]
    ac_rfl

theorem boxHostMap_add (r : Nat) (w : List HostLetter) (v u : BoxVector r) :
    boxHostMap r w (v+u)=boxHostMap r w v+boxHostMap r w u+boxHostMap r w 0 := by
  funext i
  simp only [boxHostMap,boxDecode,hostRow_sound,rowValue,←Bool.add_eq_xor,Pi.add_apply]
  have hp : parity (bit (boxEncode (v+u))) (hostRow w (boxPoint i)).sources=
      parity (bit (boxEncode v)) (hostRow w (boxPoint i)).sources+
        parity (bit (boxEncode u)) (hostRow w (boxPoint i)).sources := by
    rw [show bit (boxEncode (v+u))=bit (boxEncode v)+bit (boxEncode u) from
      funext (boxEncode_add_bit v u),parity_add]
  have hz : parity (bit (boxEncode (0:BoxVector r))) (hostRow w (boxPoint i)).sources=false := by
    induction (hostRow w (boxPoint i)).sources with
    | nil => rfl
    | cons y ys ih => simp only [parity,boxEncode_zero_bit,ih,Bool.false_xor]
  rw [hp,hz]
  cases (hostRow w (boxPoint i)).constant <;>
    cases parity (bit (boxEncode v)) (hostRow w (boxPoint i)).sources <;>
    cases parity (bit (boxEncode u)) (hostRow w (boxPoint i)).sources <;> rfl

def boxHostLinear (r : Nat) (w : List HostLetter) : BoxVector r →ₗ[Bool] BoxVector r where
  toFun v := boxHostMap r w v+boxHostMap r w 0
  map_add' v u := by
    rw [boxHostMap_add]
    ext i
    simp only [Pi.add_apply]
    cases boxHostMap r w v i <;> cases boxHostMap r w u i <;> cases boxHostMap r w 0 i <;> rfl
  map_smul' c v := by
    cases c
    · change boxHostMap r w ((0:Bool) • v)+boxHostMap r w 0=(0:Bool) • _
      ext i
      simp only [zero_smul,Pi.add_apply,Pi.zero_apply]
      cases boxHostMap r w 0 i <;> rfl
    · change boxHostMap r w ((1:Bool) • v)+boxHostMap r w 0=(1:Bool) • _
      simp only [one_smul]

def boxHostAffineMap (r : Nat) (w : List HostLetter) : BoxVector r →ᵃ[Bool] BoxVector r where
  toFun := boxHostMap r w
  linear := boxHostLinear r w
  map_vadd' u v := by
    change boxHostMap r w (v+u)=(boxHostMap r w v+boxHostMap r w 0)+boxHostMap r w u
    rw [boxHostMap_add]
    ac_rfl

def boxHostAffine (r : Nat) (w : List HostLetter) (hw : BoxFixed r w) :
    BoxVector r ≃ᵃ[Bool] BoxVector r :=
  AffineEquiv.ofBijective (φ:=boxHostAffineMap r w) (boxHostPerm r w hw).bijective

theorem boxHostAffine_apply (r : Nat) (w : List HostLetter) (hw : BoxFixed r w) (v : BoxVector r) :
    boxHostAffine r w hw v=boxHostMap r w v := rfl

theorem boxFixed_append {r : Nat} {u v : List HostLetter} (hu : BoxFixed r u) (hv : BoxFixed r v) :
    BoxFixed r (u++v) := by
  intro x y hy
  rw [hostEval_append,Equiv.Perm.mul_apply,hu _ y hy,hv x y hy]

theorem boxHostAffine_append {r : Nat} {u v : List HostLetter} (hu : BoxFixed r u) (hv : BoxFixed r v) :
    boxHostAffine r (u++v) (boxFixed_append hu hv)=boxHostAffine r u hu*boxHostAffine r v hv := by
  ext x i
  change boxDecode r (hostEval (u++v) (boxEncode x)) i=
    boxDecode r (hostEval u (boxEncode (boxHostMap r v x))) i
  rw [boxHostMap_encode hv,hostEval_append]
  rfl

theorem boxHostAffine_eq {r : Nat} {u v : List HostLetter} (hu : BoxFixed r u) (hv : BoxFixed r v)
    (he : hostEval u=hostEval v) : boxHostAffine r u hu=boxHostAffine r v hv := by
  ext x i
  change boxDecode r (hostEval u (boxEncode x)) i=boxDecode r (hostEval v (boxEncode x)) i
  rw [he]

theorem boxHostAffine_identity {r : Nat} {w : List HostLetter} (hw : BoxFixed r w)
    (he : hostEval w=1) : boxHostAffine r w hw=1 := by
  ext x i
  change boxDecode r (hostEval w (boxEncode x)) i=x i
  rw [he]
  exact congrFun (boxDecode_encode x) i

theorem boxHostAffine_inverse {r : Nat} {w : List HostLetter} (hw : BoxFixed r w) :
    boxHostAffine r (inverseHostWord w) (boxFixed_inverse hw)=(boxHostAffine r w hw).symm := by
  ext x i
  have hh : boxHostAffine r (inverseHostWord w) (boxFixed_inverse hw) x=(boxHostAffine r w hw).symm x := by
    apply (boxHostAffine r w hw).injective
    rw [AffineEquiv.apply_symm_apply]
    change boxDecode r (hostEval w (boxEncode (boxHostMap r (inverseHostWord w) x)))=x
    rw [boxHostMap_encode (boxFixed_inverse hw),hostEval_inverse]
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using boxDecode_encode x
  exact congrFun hh i

def boxVectorEquiv (r : Nat) : BoxVector r ≃ₗ[Bool] (Fin (3*r) → Bool) :=
  LinearEquiv.piCongrLeft' Bool (fun _ : BoxIndex r => Bool) finProdFinEquiv

def finiteHostAffine (r : Nat) (w : List HostLetter) (hw : BoxFixed r w) :
    (Fin (3*r) → Bool) ≃ᵃ[Bool] (Fin (3*r) → Bool) :=
  (boxVectorEquiv r).symm.toAffineEquiv.trans ((boxHostAffine r w hw).trans (boxVectorEquiv r).toAffineEquiv)

theorem finiteHostAffine_encode (r : Nat) (w : List HostLetter) (hw : BoxFixed r w)
    (v : Fin (3*r) → Bool) :
    boxEncode ((boxVectorEquiv r).symm (finiteHostAffine r w hw v))=
      hostEval w (boxEncode ((boxVectorEquiv r).symm v)) := by
  change boxEncode ((boxVectorEquiv r).symm ((boxVectorEquiv r)
    (boxHostMap r w ((boxVectorEquiv r).symm v))))=_
  rw [LinearEquiv.symm_apply_apply,boxHostMap_encode hw]

theorem finiteHostAffine_identity {r : Nat} {w : List HostLetter} (hw : BoxFixed r w)
    (he : hostEval w=1) : finiteHostAffine r w hw=1 := by
  rw [finiteHostAffine,boxHostAffine_identity hw he]
  ext x i
  exact congrFun ((boxVectorEquiv r).apply_symm_apply x) i

theorem hostClockCocycle_boxFixed (a : HostLetter) (c : Clock) (m : Nat)
    (h1 : c.1.natAbs≤m) (h2 : c.2.1.natAbs≤m)
    (h3 : (clockMove a c).1.natAbs≤m) (h4 : (clockMove a c).2.1.natAbs≤m) :
    BoxFixed (2*m+3) (hostClockCocycle a c) := by
  intro v y hy
  rw [hostRow_sound,hostClockCocycle_support a c m h1 h2 h3 h4 y hy]
  simp only [rowValue,parity,Bool.xor_false,Bool.false_xor]

end
end Blueprint.AHash

#print axioms Blueprint.AHash.boxRay
#print axioms Blueprint.AHash.BoxIndex
#print axioms Blueprint.AHash.BoxVector
#print axioms Blueprint.AHash.boxPoint
#print axioms Blueprint.AHash.boxPoint_injective
#print axioms Blueprint.AHash.boxEncode
#print axioms Blueprint.AHash.boxDecode
#print axioms Blueprint.AHash.boxCoord
#print axioms Blueprint.AHash.boxPoint_coord
#print axioms Blueprint.AHash.boxEncode_bit
#print axioms Blueprint.AHash.boxEncode_outside
#print axioms Blueprint.AHash.boxDecode_encode
#print axioms Blueprint.AHash.BoxSupported
#print axioms Blueprint.AHash.boxEncode_supported
#print axioms Blueprint.AHash.boxEncode_decode
#print axioms Blueprint.AHash.hostEval_append
#print axioms Blueprint.AHash.hostGenerator_inverse
#print axioms Blueprint.AHash.hostEval_inverse
#print axioms Blueprint.AHash.BoxFixed
#print axioms Blueprint.AHash.boxFixed_supported
#print axioms Blueprint.AHash.boxFixed_inverse
#print axioms Blueprint.AHash.boxHostMap
#print axioms Blueprint.AHash.boxHostMap_encode
#print axioms Blueprint.AHash.boxHostPerm
#print axioms Blueprint.AHash.boxEncode_add_bit
#print axioms Blueprint.AHash.boxEncode_zero_bit
#print axioms Blueprint.AHash.parity_add
#print axioms Blueprint.AHash.boxHostMap_add
#print axioms Blueprint.AHash.boxHostLinear
#print axioms Blueprint.AHash.boxHostAffineMap
#print axioms Blueprint.AHash.boxHostAffine
#print axioms Blueprint.AHash.boxHostAffine_apply
#print axioms Blueprint.AHash.boxFixed_append
#print axioms Blueprint.AHash.boxHostAffine_append
#print axioms Blueprint.AHash.boxHostAffine_eq
#print axioms Blueprint.AHash.boxHostAffine_identity
#print axioms Blueprint.AHash.boxHostAffine_inverse
#print axioms Blueprint.AHash.boxVectorEquiv
#print axioms Blueprint.AHash.finiteHostAffine
#print axioms Blueprint.AHash.finiteHostAffine_encode
#print axioms Blueprint.AHash.finiteHostAffine_identity
#print axioms Blueprint.AHash.hostClockCocycle_boxFixed
