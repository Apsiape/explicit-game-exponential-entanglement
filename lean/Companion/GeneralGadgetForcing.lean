import Companion.GeneralGadgetData

namespace Companion.GeneralGadget

structure Solution {p : Input} {G : Type} [Group G] (X : Variable p → G) (J : G) : Prop where
  square : ∀ a, X a*X a=1
  j_square : J*J=1
  central : ∀ a, Commute (X a) J
  product : ∀ e, (if (systemEquation p e).rhs then J else 1)*
    (((systemEquation p e).vars).map X).prod=1
  commutation : ∀ e a b, a ∈ (systemEquation p e).vars → b ∈ (systemEquation p e).vars →
    Commute (X a) (X b)

private theorem solve3 {G : Type} [Group G] {a b c : G} (ha : a*a=1) (he : a*b*c=1) : a=b*c := by
  apply mul_left_cancel (a:=a)
  simpa only [← mul_assoc,ha,one_mul,mul_one] using he.symm

private theorem conjugate_product {G : Type} [Group G] (a b c : G) (ha : a*a=1) :
    (a*b*a)*(a*c*a)=a*(b*c)*a := by
  calc
    _ = (a*b)*((a*a)*(c*a)) := by simp only [mul_assoc]
    _ = _ := by rw [ha,one_mul]; simp only [mul_assoc]

/-- Exact recovery of one old conjugacy relation from the nice presentation. -/
theorem nice_forcing {G : Type} [Group G] (a b c g abar bp bpp cp cpp : G)
    (ha : a*a=1) (hb : b*b=1) (hc : c*c=1) (hg : g*g=1) (hbar : abar*abar=1)
    (eA : a*g*abar=1) (eB : b*bp*bpp=1) (eC : c*cp*cpp=1)
    (hgb : Commute g abar) (hgcp : g*cp*g=cpp)
    (hbp : abar*bp*abar=cpp) (hbpp : abar*bpp*abar=cp) : a*b*a=c := by
  have aeq := solve3 ha eA
  have beq := solve3 hb eB
  have ceq := solve3 hc eC
  have ag : a=abar*g := aeq.trans hgb.eq
  have hgcpp : g*cpp*g=cp := by
    rw [← hgcp]
    calc
      _ = (g*g)*cp*(g*g) := by simp only [mul_assoc]
      _ = cp := by rw [hg,one_mul,mul_one]
  calc
    a*b*a = (g*abar)*(bp*bpp)*(abar*g) := by rw [← aeq,← beq,← ag]
    _ = g*(abar*(bp*bpp)*abar)*g := by simp only [mul_assoc]
    _ = g*((abar*bp*abar)*(abar*bpp*abar))*g := by rw [conjugate_product _ _ _ hbar]
    _ = g*(cpp*cp)*g := by rw [hbp,hbpp]
    _ = (g*cpp*g)*(g*cp*g) := (conjugate_product _ _ _ hg).symm
    _ = cp*cpp := by rw [hgcpp,hgcp]
    _ = c := ceq.symm

variable {p : Input} {G : Type} [Group G] {X : Variable p → G} {J : G}

theorem Solution.nice_conjugacy (h : Solution X J) (t : NiceTriple p) :
    let (a,b,c) := niceTriple p t
    X (old a)*X (old b)*X (old a)=X (old c) := by
  rcases ht : niceTriple p t with ⟨a,b,c⟩
  dsimp
  have eqn (k : Fin 6) := h.product (.inr (t,k))
  have hc := h.commutation (.inr (t,4)) (lamp t 5) (lamp t 6)
    (by simp [systemEquation]) (by simp [systemEquation])
  exact six_equation_forcing G (X (old a)) (X (old b)) (X (old c))
    (X (lamp t 0)) (X (lamp t 1)) (X (lamp t 2)) (X (lamp t 3))
    (X (lamp t 4)) (X (lamp t 5)) (X (lamp t 6))
    (h.square _) (h.square _) (h.square _) (h.square _) (h.square _) (h.square _)
    (h.square _) (h.square _) (h.square _) (h.square _)
    (by simpa [systemEquation,ht,← mul_assoc] using eqn 0)
    (by simpa [systemEquation,ht,← mul_assoc] using eqn 1)
    (by simpa [systemEquation,ht,← mul_assoc] using eqn 2)
    (by simpa [systemEquation,ht,← mul_assoc] using eqn 3)
    (by simpa [systemEquation,ht,← mul_assoc] using eqn 4)
    (by simpa [systemEquation,ht,← mul_assoc] using eqn 5) hc.eq

theorem Solution.base_product (h : Solution X J) (e : BaseEquation p) :
    (if (niceEquation p e).rhs then J else 1)*
      ((niceEquation p e).vars.map (fun a => X (old a))).prod=1 := by
  cases hr : (niceEquation p e).rhs <;>
    simpa [systemEquation,hr,List.map_map,Function.comp_def] using h.product (.inl e)

theorem Solution.base_commutation (h : Solution X J) (e : BaseEquation p) (a b : Nice p)
    (ha : a ∈ (niceEquation p e).vars) (hb : b ∈ (niceEquation p e).vars) :
    Commute (X (old a)) (X (old b)) := by
  apply h.commutation (.inl e)
  · exact List.mem_map.mpr ⟨a,ha,rfl⟩
  · exact List.mem_map.mpr ⟨b,hb,rfl⟩

/-- All conjugacies of the Step-2 presentation follow in the final solution group. -/
theorem Solution.host_conjugacy (h : Solution X J) (t : HostTriple p) :
    let (a,b,c) := hostTriple p t
    X (old (nOld a))*X (old (nOld b))*X (old (nOld a))=X (old (nOld c)) := by
  rcases ht : hostTriple p t with ⟨a,b,c⟩
  dsimp
  have ep (v : Host p) := h.base_product (.inr (.inr (.inl (v,false))))
  have eg (v : Host p) := h.base_product (.inr (.inr (.inl (v,true))))
  apply nice_forcing (X (old (nOld a))) (X (old (nOld b))) (X (old (nOld c)))
    (X (old (nG p))) (X (old (nBar a))) (X (old (nPrime b))) (X (old (nDPrime b)))
    (X (old (nPrime c))) (X (old (nDPrime c)))
    (h.square _) (h.square _) (h.square _) (h.square _) (h.square _)
  · simpa [niceEquation,← mul_assoc] using eg a
  · simpa [niceEquation,← mul_assoc] using ep b
  · simpa [niceEquation,← mul_assoc] using ep c
  · exact h.base_commutation (.inr (.inr (.inl (a,true)))) _ _
      (by simp [niceEquation]) (by simp [niceEquation])
  · simpa [niceTriple] using h.nice_conjugacy (.inl c)
  · simpa [niceTriple,ht] using h.nice_conjugacy (.inr (t,false))
  · simpa [niceTriple,ht] using h.nice_conjugacy (.inr (t,true))

def evaluateFinal (X : Variable p → G) (J : G) : FreeGroup (Option (Variable p)) →* G :=
  FreeGroup.lift (fun a => a.elim J X)
def evaluateSource (X : Variable p → G) (J : G) : FreeGroup (Source p) →* G :=
  (evaluateFinal X J).comp (substitution p)

@[simp] theorem evaluateSource_old (a : Fin p.n0) :
    evaluateSource X J (srcOld a)=X (old (nOld (hOld a))) := by
  simp [evaluateSource,evaluateFinal,substitution,sourceImages,srcOld]
@[simp] theorem evaluateSource_y (a : Fin p.yCount) :
    evaluateSource X J (srcY a)=X (old (nOld (hF a)))*X (old (nOld (hV a))) := by
  simp [evaluateSource,evaluateFinal,substitution,sourceImages,srcY]

theorem Solution.source_relators (h : Solution X J) (i : SourceRel p) :
    evaluateSource X J (sourceRelator p i)=1 := by
  rcases i with a|i
  · simpa [sourceRelator] using h.square (old (nOld (hOld a)))
  · rcases i with i|i
    · have hr := h.base_product (.inl i)
      simpa [sourceRelator,niceEquation,map_list_prod,List.map_map,Function.comp_def] using hr
    · rcases i with i|i
      · have hc := h.host_conjugacy (.inl i)
        simpa [sourceRelator,hostTriple,map_mul,map_inv] using
          congrArg (fun v => v*(X (old (nOld (hOld (p.c0[i]).2.2))))⁻¹) hc
      · have hv := h.host_conjugacy (.inr (.inl (i,false)))
        have hf := h.host_conjugacy (.inr (.inl (i,true)))
        let F := X (old (nOld (hF (p.yIndex i))))
        let V := X (old (nOld (hV (p.yIndex i))))
        have hFi : F⁻¹=F := inv_eq_of_mul_eq_one_left (h.square _)
        have hVi : V⁻¹=V := inv_eq_of_mul_eq_one_left (h.square _)
        have he : (F*V)*X (old (nOld (hOld (p.c1[i]).1)))*(F*V)⁻¹=
            X (old (nOld (hOld (p.c1[i]).2))) := by
          rw [mul_inv_rev,hFi,hVi]
          calc
            _ = F*(V*X (old (nOld (hOld (p.c1[i]).1)))*V)*F := by simp only [mul_assoc]
            _ = F*X (old (nOld (hZ i)))*F := by
              simpa [hostTriple,F,V] using congrArg (fun v => F*v*F) hv
            _ = _ := by simpa [hostTriple,F] using hf
        simpa [sourceRelator,map_mul,map_inv,F,V] using
          congrArg (fun v => v*(X (old (nOld (hOld (p.c1[i]).2))))⁻¹) he

theorem Solution.distinguished_relation (h : Solution X J) :
    evaluateFinal X J (distinguishedWord p)=1 := by
  let W := X (old (nOld (hOld p.distinguished)))
  let T := X (old (nOld (hT p)))
  let U := X (old (nOld (hU p)))
  have hc : T*W*T=U := by
    simpa [hostTriple,T,W,U] using h.host_conjugacy (.inr (.inr ()))
  have hw : W⁻¹=W := inv_eq_of_mul_eq_one_left (h.square _)
  have ht : T⁻¹=T := inv_eq_of_mul_eq_one_left (h.square _)
  have hp : J*(W*U)=1 := by
    simpa [niceEquation,W,U] using h.base_product (.inr (.inl ()))
  have hwu : W*U=J := by
    calc
      W*U = (J*J)*(W*U) := by rw [h.j_square,one_mul]
      _ = J*(J*(W*U)) := by simp only [mul_assoc]
      _ = J := by rw [hp,mul_one]
  simp only [distinguishedWord,map_mul,map_inv,evaluateFinal,FreeGroup.lift_apply_of,Option.elim_some,
    Option.elim_none]
  change W*T*W⁻¹*T⁻¹*J=1
  rw [hw,ht]
  calc
    W*T*W*T*J = W*(T*W*T)*J := by simp only [mul_assoc]
    _ = W*U*J := by rw [hc]
    _ = 1 := by rw [hwu,h.j_square]

end Companion.GeneralGadget
