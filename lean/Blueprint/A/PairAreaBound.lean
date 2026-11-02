import Blueprint.A.Clearing

namespace Blueprint.PairProof
open Companion ASector
open scoped BigOperators

/-- A global pair filling from local translation and transvection fillings.
The proof normalizes after each clearing step and records every area cost. -/
theorem pair_area_bound {α ι : Type} {R : ι → FreeGroup α} (n L : Nat) (hn : 1≤n) (hL : 1≤L)
    (t : Fin n → FreeGroup α) (X : Fin n → Fin n → FreeGroup α)
    (hsq : ∀ k, FiniteArea.Area R (t k*t k) 1)
    (hc : ∀ k l, FiniteArea.Area R (groupComm (t k) (t l)) L)
    (hX : ∀ i j, i≠j → ∀ k,
      Close R (X i j*t k*(X i j)⁻¹) (Function.update t j (t j*t i) k) L)
    (a b : FreeGroup α)
    (hXa : ∀ i j, i≠j → FiniteArea.Area R (groupComm (X i j) a) L)
    (hXb : ∀ i j, i≠j → FiniteArea.Area R (groupComm (X i j) b) L)
    (hnear : ∀ j, FiniteArea.Area R (groupComm a (t j*b*(t j)⁻¹)) L)
    (u v : Fin n → Bool) (hne : u≠v) :
    FiniteArea.Area R (groupComm (cube n t u*a*(cube n t u)⁻¹)
      (cube n t v*b*(cube n t v)⁻¹)) (100*n^3*L) := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, u j≠v j := by
    by_contra hh
    push_neg at hh
    exact hne (funext hh)
  let w := fun k => u k ^^ v k
  have hw : w j=true := by
    dsimp [w]
    cases hu : u j <;> cases hv : v j <;> simp_all
  obtain ⟨G,hG,hGcomm⟩ := clear_all t (fun i => X i j) j L L hL hsq hc (fun i hi => hX i j hi) w hw
  have hGa := hGcomm a (fun i hi => hXa i j hi)
  have hGb := hGcomm b (fun i hi => hXb i j hi)
  have hGa' : Close R (G*a*G⁻¹) a (n*L) := by simpa [Close,groupComm] using hGa
  have hGb' : Close R (G*b*G⁻¹) b (n*L) := by simpa [Close,groupComm] using hGb
  let T := cube n t w
  let D := 5*n^3*L
  have hinner := close_mul (close_mul hG hGb') (close_inv hG)
  have hcom := close_comm hGa' hinner
  have he : groupComm (G*a*G⁻¹)
      ((G*T*G⁻¹)*(G*b*G⁻¹)*(G*T*G⁻¹)⁻¹)=G*groupComm a (T*b*T⁻¹)*G⁻¹ := by
    dsimp [groupComm]
    group
  change Close R (groupComm (G*a*G⁻¹)
    ((G*T*G⁻¹)*(G*b*G⁻¹)*(G*T*G⁻¹)⁻¹)) (groupComm a (t j*b*(t j)⁻¹)) _ at hcom
  rw [he] at hcom
  have hnear' := (close_to_one (R:=R) (a:=groupComm a (t j*b*(t j)⁻¹)) (k:=L)).mpr (hnear j)
  have hg := close_trans hcom hnear'
  have harea := area_conj G⁻¹ (close_to_one.mp hg)
  have harea' : FiniteArea.Area R (groupComm a (T*b*T⁻¹))
      (2*(n*L)+2*((D+n*L)+D)+L) := by
    convert harea using 1
    dsimp [T]
    group
  let A := cube n t u
  let B := cube n t v
  let C := n^2*L+n
  have hinv := cube_inverse_close n t L hsq hc u
  have hfirst := close_mul hinv (close_refl R B)
  have hsecond := cube_mul_close n t L hsq hc u v
  have hZ : Close R (A⁻¹*B) T (2*C) := by
    have hh := close_trans hfirst hsecond
    simpa only [A,B,C,T,w,Nat.add_zero,two_mul] using hh
  have hconj := close_conjugator b hZ
  have hcomm := close_comm (close_refl R a) hconj
  have hfinal := close_trans hcomm (close_to_one.mpr harea')
  have htransport := area_conj A (close_to_one.mp hfinal)
  have heq : A*groupComm a ((A⁻¹*B)*b*(A⁻¹*B)⁻¹)*A⁻¹=
      groupComm (A*a*A⁻¹) (B*b*B⁻¹) := by
    dsimp [groupComm]
    group
  rw [heq] at htransport
  apply area_weaken htransport
  have h12 : n≤n^2 := by nlinarith
  have h23 : n^2≤n^3 := Nat.pow_le_pow_right hn (by decide)
  have hnL : n≤n*L := by simpa using Nat.mul_le_mul_left n hL
  have h12L := Nat.mul_le_mul_right L h12
  have h23L := Nat.mul_le_mul_right L h23
  have hpos : 1≤n^3*L := by
    have hh : 0<n^3*L := by positivity
    omega
  dsimp [C,D]
  nlinarith only [hnL,h12L,h23L,hpos]

end Blueprint.PairProof

#print axioms Blueprint.PairProof.pair_area_bound
