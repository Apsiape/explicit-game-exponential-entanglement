import Blueprint.A.StabilizerWords

namespace Blueprint.PairProof
noncomputable section
open Companion ASector Published

/-- A bounded finite permutation fixing the prototype has a short word in
the actual two stabilizer generators of the certificate. -/
theorem finite_stabilizer_word (k n : Nat) (hk : k=1 ∨ k=2)
    (S : Finset Concrete.Point) (g : Equiv.Perm Concrete.Point)
    (hg : ∀ y, g y≠y → y∈S)
    (hS : ∀ y∈S, y.1=Concrete.Ray.one ∧ k≤y.2 ∧ y.2<n) :
    ∃ w : Word, w.length≤10*n*(S.card-1) ∧
      (∀ a∈w, a.1∈[1,2]) ∧
      pointHom (stabilizerHom k (FreeGroup.mk w))=g := by
  obtain ⟨xs,hl,hm,hp⟩ := finite_swap_factorization S g hg
  let word := fun a : Concrete.Point × Concrete.Point => omegaWord (a.1.2-k) (a.2.2-k)
  have ha (a : Concrete.Point × Concrete.Point) (h : a.1∈S ∧ a.2∈S) :
      pointHom (stabilizerHom k (FreeGroup.mk (word a)))=Equiv.swap a.1 a.2 := by
    obtain ⟨hi,hik,hin⟩ := hS a.1 h.1
    obtain ⟨hj,hjk,hjn⟩ := hS a.2 h.2
    have he := stabilizer_omega k hk a.1.2 a.2.2 hik hjk
    have hpa : (Concrete.Ray.one,a.1.2)=a.1 := Prod.ext hi.symm rfl
    have hpb : (Concrete.Ray.one,a.2.2)=a.2 := Prod.ext hj.symm rfl
    simpa only [word,hpa,hpb] using he
  have hall : ∀ ys : List (Concrete.Point × Concrete.Point),
      (∀ a∈ys, a.1∈S ∧ a.2∈S) →
      ((ys.map word).flatten).length≤10*n*ys.length ∧
      (∀ a∈(ys.map word).flatten, a.1∈[1,2]) ∧
      pointHom (stabilizerHom k (FreeGroup.mk (ys.map word).flatten))=
        (ys.map (fun a => Equiv.swap a.1 a.2)).prod := by
    intro ys
    induction ys with
    | nil => intro _; simp [←FreeGroup.one_eq_mk]
    | cons a ys ih =>
      intro hys
      have hhead := hys a (by simp)
      have ht := ih (fun b hb => hys b (by simp [hb]))
      have hlen : (word a).length≤10*n := by
        exact Nat.le_of_lt (omega_length _ _ n (by have := (hS a.1 hhead.1).2.2; omega)
          (by have := (hS a.2 hhead.2).2.2; omega))
      refine ⟨?_,?_,?_⟩
      · simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
        omega
      · intro b hb
        simp only [List.map_cons,List.flatten_cons,List.mem_append] at hb
        rcases hb with hb|hb
        · exact omega_letters _ _ b hb
        · exact ht.2.1 b hb
      · simp only [List.map_cons,List.flatten_cons,←FreeGroup.mul_mk,map_mul,ha a hhead,
          ht.2.2,List.prod_cons]
  have hf := hall xs hm
  exact ⟨(xs.map word).flatten,hf.1.trans (Nat.mul_le_mul_left _ hl),hf.2.1,hf.2.2.trans hp⟩

end
end Blueprint.PairProof

#print axioms Blueprint.PairProof.finite_stabilizer_word
