import Companion.ReturnParityCorrection

namespace Companion.Analytic.ReturnProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def rowIndex (g : LCS) (i : Fin g.system.equations.length) :
    Fin (g.system.equations[i.val]).vars.length ↪ Fin g.system.n where
  toFun k := ⟨(g.system.equations[i.val]).vars[k.val],
    TransferProof.row_variable_bound g i _ (List.getElem_mem k.isLt)⟩
  inj' := by
    intro k l h
    exact (List.nodup_iff_injective_get.mp
      (g.rows_nodup _ (List.getElem_mem i.isLt))) (congrArg Fin.val h)

theorem rowIndex_range (g : LCS) (i : Fin g.system.equations.length) (j : Fin g.system.n) :
    (∃ k, rowIndex g i k=j) ↔ j.val∈(g.system.equations[i.val]).vars := by
  constructor
  · rintro ⟨k,rfl⟩
    exact List.getElem_mem k.isLt
  · intro hj
    obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hj
    exact ⟨⟨k,hk⟩,Fin.ext he⟩

def rowRecord (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin (g.system.equations[i.val]).vars.length → Bool) : Fin g.system.n → Bool :=
  Function.extend (rowIndex g i) a (fun _ => false)

theorem rowRecord_apply (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin (g.system.equations[i.val]).vars.length → Bool) (k) :
    rowRecord g i a (rowIndex g i k)=a k :=
  (rowIndex g i).injective.extend_apply a _ k

theorem rowRecord_unasked (g : LCS) (i : Fin g.system.equations.length)
    (a : Fin (g.system.equations[i.val]).vars.length → Bool) (j : Fin g.system.n)
    (hj : j.val∉(g.system.equations[i.val]).vars) : rowRecord g i a j=false := by
  exact Function.extend_apply' a _ j (fun h => hj ((rowIndex_range g i j).mp h))

def rowRecordEquiv (g : LCS) (i : Fin g.system.equations.length) :
    (Fin (g.system.equations[i.val]).vars.length → Bool) ≃
      {a : Fin g.system.n → Bool // ∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false} where
  toFun a := ⟨rowRecord g i a,rowRecord_unasked g i a⟩
  invFun a := fun k => a.val (rowIndex g i k)
  left_inv a := by funext k; exact rowRecord_apply g i a k
  right_inv a := by
    apply Subtype.ext
    funext j
    change rowRecord g i (fun k => a.val (rowIndex g i k)) j=a.val j
    by_cases hj : j.val∈(g.system.equations[i.val]).vars
    · obtain ⟨k,rfl⟩ := (rowIndex_range g i j).mpr hj
      exact rowRecord_apply g i _ k
    · rw [rowRecord_unasked g i _ j hj,a.property j hj]

theorem jointProjection_reverseProd {d : Nat} (n : Nat) (C : Fin n → Mat d) (a : Fin n → Bool) :
    CountProof.jointProjection n C a=
      ((List.ofFn fun k => signProjection (C k) (a k)).reverse).prod := by
  induction n with
  | zero => simp [CountProof.jointProjection]
  | succ n ih =>
    simp only [CountProof.jointProjection,List.ofFn_succ,List.reverse_cons,List.prod_append,
      List.prod_cons,List.prod_nil,Matrix.mul_one]
    rw [ih]
    rfl

theorem sequentialKraus_rowRecord {d : Nat} (g : LCS) (B : Fin g.system.n → Mat d)
    (i : Fin g.system.equations.length) (a : Fin (g.system.equations[i.val]).vars.length → Bool) :
    sequentialKraus g B i (rowRecord g i a)=
      CountProof.jointProjection _ (fun k => (B (rowIndex g i k)).transpose) a := by
  rw [jointProjection_reverseProd]
  unfold sequentialKraus
  congr 2
  conv_lhs => rw [← List.ofFn_getElem (xs:=(g.system.equations[i.val]).vars)]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  have hk := (rowIndex g i k).isLt
  change (g.system.equations[i.val]).vars[k.val]<g.system.n at hk
  change (if h : (g.system.equations[i.val]).vars[k.val]<g.system.n then
    signProjection (B ⟨_,h⟩).transpose (rowRecord g i a ⟨_,h⟩) else 1)=_
  rw [dif_pos hk]
  rw [show (⟨(g.system.equations[i.val]).vars[k.val],hk⟩ : Fin g.system.n)=rowIndex g i k from rfl]
  rw [rowRecord_apply]

theorem sum_canonical_records {z : Type*} [AddCommMonoid z] (g : LCS)
    (i : Fin g.system.equations.length) (F : (Fin g.system.n → Bool) → z) :
    (∑ a, if (∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false) then F a else 0)=
      ∑ a, F (rowRecord g i a) := by
  classical
  calc
    _=∑ a : {a : Fin g.system.n → Bool // ∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false}, F a.val := by
      let p := fun a : Fin g.system.n → Bool => ∀ j, j.val∉(g.system.equations[i.val]).vars → a j=false
      have h := Fintype.sum_subtype_add_sum_subtype p (fun a => if p a then F a else 0)
      have hy : (∑ a : {a // p a}, if p a.val then F a.val else 0)=∑ a : {a // p a}, F a.val :=
        Finset.sum_congr rfl (fun a _ => if_pos a.property)
      have hn : (∑ a : {a // ¬p a}, if p a.val then F a.val else 0)=0 := by
        apply Finset.sum_eq_zero
        intro a _
        exact if_neg a.property
      rw [hy,hn,add_zero] at h
      exact h.symm
    _=_ := (Equiv.sum_comp (rowRecordEquiv g i) (fun a => F a.val)).symm

end
end Companion.Analytic.ReturnProof
