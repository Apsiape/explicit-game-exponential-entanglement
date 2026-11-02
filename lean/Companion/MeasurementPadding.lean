import Companion.ProfileDimensionEntropy

namespace Companion.Analytic.ProfileProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

def paddedEffect {r d : Nat} {a : Type*} [DecidableEq a]
    (V : Matrix (Fin d) (Fin r) ℂ) (E : a → Mat r) (a0 a : a) : Mat d :=
  V*E a*V.conjTranspose+if a=a0 then 1-V*V.conjTranspose else 0

theorem paddedEffect_positive {r d : Nat} {a : Type*} [DecidableEq a]
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (E : a → Mat r) (hE : ∀ a, (E a).PosSemidef) (a0 a : a) :
    (paddedEffect V E a0 a).PosSemidef := by
  apply (hE a).mul_mul_conjTranspose_same V |>.add
  by_cases ha : a=a0
  · rw [ite_eq_left ha]
    exact TransferProof.isometry_complement_positive V hV
  · rw [ite_eq_right ha]
    exact Matrix.PosSemidef.zero

theorem paddedEffect_complete {r d : Nat} {a : Type*} [Fintype a] [DecidableEq a]
    (V : Matrix (Fin d) (Fin r) ℂ) (E : a → Mat r) (hE : ∑ a, E a=1) (a0 : a) :
    (∑ a, paddedEffect V E a0 a)=1 := by
  simp only [paddedEffect,Finset.sum_add_distrib]
  have he : (∑ a, V*E a*V.conjTranspose)=V*(∑ a, E a)*V.conjTranspose := by
    simp only [Matrix.mul_sum,Matrix.sum_mul]
  rw [he,hE,Matrix.mul_one]
  have hs : (∑ a : a, if a=a0 then (1-V*V.conjTranspose) else 0)=1-V*V.conjTranspose := by
    rw [Finset.sum_eq_single a0]
    · exact ite_eq_left rfl
    · intro b _ hb
      exact ite_eq_right hb
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [hs]
  abel

theorem paddedEffect_compression {r d : Nat} {a : Type*} [DecidableEq a]
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (E : a → Mat r) (a0 a : a) : V.conjTranspose*paddedEffect V E a0 a*V=E a := by
  have hc : V.conjTranspose*(1-V*V.conjTranspose)*V=0 := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.mul_assoc,hV,
      Matrix.one_mul,Matrix.mul_one,sub_self]
  have he : V.conjTranspose*(V*E a*V.conjTranspose)*V=E a := by
    calc
      _=(V.conjTranspose*V)*E a*(V.conjTranspose*V) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hV,Matrix.one_mul,Matrix.mul_one]
  by_cases ha : a=a0
  · rw [paddedEffect,ite_eq_left ha,Matrix.mul_add,Matrix.add_mul,he,hc,add_zero]
  · simpa only [paddedEffect,ha,↓reduceIte,add_zero] using he

def paddingAnswer (g : LCS) (i : Fin g.system.equations.length) : Fin g.system.n → Bool :=
  correctedAnswer g i (fun _ => false)

theorem paddingAnswer_valid (g : LCS) (i : Fin g.system.equations.length) :
    validAnswer g i (paddingAnswer g i) := ReturnProof.correctedAnswer_valid g i _

def paddedStrategy {g : LCS} {r d : Nat} (s : Strategy g r r)
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1) : Strategy g d d where
  psi := V*s.psi*V.transpose
  normalized := by
    change hsNorm (V*s.psi*V.transpose)=1
    rw [TransferProof.hsNorm_coisometry_right _ _ (TransferProof.transpose_isometry_coisometry V hV),
      hsNorm_isometry_left V s.psi hV]
    exact s.normalized
  alice i := paddedEffect V (s.alice i) (paddingAnswer g i)
  alice_positive i := paddedEffect_positive V hV _ (s.alice_positive i) _
  alice_complete i := paddedEffect_complete V _ (s.alice_complete i) _
  alice_valid i a ha := by
    have hne : a≠paddingAnswer g i := fun h => ha (h ▸ paddingAnswer_valid g i)
    simp only [paddedEffect,s.alice_valid i a ha,hne,↓reduceIte,Matrix.mul_zero,Matrix.zero_mul,add_zero]
  bob j := paddedEffect V (s.bob j) false
  bob_positive j := paddedEffect_positive V hV _ (s.bob_positive j) _
  bob_complete j := by
    have hc : (∑ b, s.bob j b)=1 := by simpa only [Fintype.sum_bool] using s.bob_complete j
    simpa only [Fintype.sum_bool] using paddedEffect_complete V _ hc false

theorem paddedStrategy_expectation {g : LCS} {r d : Nat} (s : Strategy g r r)
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (i : Fin g.system.equations.length) (a : Fin g.system.n → Bool) (j : Fin g.system.n) (b : Bool) :
    expectation (paddedStrategy s V hV).psi ((paddedStrategy s V hV).alice i a)
      ((paddedStrategy s V hV).bob j b)=expectation s.psi (s.alice i a) (s.bob j b) := by
  change expectation ((V*s.psi)*V.transpose) (paddedEffect V (s.alice i) (paddingAnswer g i) a)
    (paddedEffect V (s.bob j) false b)=_
  rw [TransferProof.alice_embedding_expectation (V*s.psi) V _ _
    (paddedEffect_compression V hV _ _ _) _]
  have hvpsi : V.conjTranspose*(V*s.psi)=s.psi := by rw [← Matrix.mul_assoc,hV,Matrix.one_mul]
  have hsupp : V*(V.conjTranspose*(V*s.psi))=V*s.psi := by rw [hvpsi]
  have h := TransferProof.compressed_expectation (V*s.psi) V hsupp (s.alice i a) (paddedEffect V (s.bob j) false b)
  rw [hvpsi,paddedEffect_compression V hV (s.bob j) false b] at h
  exact h.symm

theorem paddedStrategy_pairWin {g : LCS} {r d : Nat} (s : Strategy g r r)
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) :
    pairWin (paddedStrategy s V hV) i j=pairWin s i j := by
  unfold pairWin
  split
  · apply Finset.sum_congr rfl
    intro a _
    exact paddedStrategy_expectation s V hV i a j (a j)
  · rfl

theorem paddedStrategy_win {g : LCS} {r d : Nat} (s : Strategy g r r)
    (V : Matrix (Fin d) (Fin r) ℂ) (hV : V.conjTranspose*V=1) :
    win (paddedStrategy s V hV)=win s := by simp only [win,paddedStrategy_pairWin]

def paddingEmbedding {r d : Nat} (hrd : r≤d) : Matrix (Fin d) (Fin r) ℂ :=
  fun i j => if Fin.castLE hrd j=i then 1 else 0

theorem paddingEmbedding_isometry {r d : Nat} (hrd : r≤d) :
    (paddingEmbedding hrd).conjTranspose*paddingEmbedding hrd=1 := by
  ext j k
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,paddingEmbedding]
  rw [Finset.sum_eq_single (Fin.castLE hrd j)]
  · by_cases hjk : j=k
    · subst k
      simp
    · have hkj : Fin.castLE hrd k≠Fin.castLE hrd j := fun h => hjk ((Fin.castLE_injective hrd h).symm)
      simp [hkj,Matrix.one_apply,hjk]
  · intro b _ hb
    have hne : Fin.castLE hrd j≠b := Ne.symm hb
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem strategy_padding {g : LCS} {r d : Nat} (s : Strategy g r r) (hrd : r≤d) :
    ∃ t : Strategy g d d, win t=win s :=
  ⟨paddedStrategy s (paddingEmbedding hrd) (paddingEmbedding_isometry hrd),
    paddedStrategy_win s _ _⟩

end
end Companion.Analytic.ProfileProof
