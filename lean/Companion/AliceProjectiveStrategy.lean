import Companion.AliceDilationData

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem transpose_isometry_coisometry {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (V : Matrix b a ℂ) (hV : V.conjTranspose*V=1) :
    V.transpose*(V.transpose).conjTranspose=1 := by
  rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,← Matrix.transpose_mul,hV,Matrix.transpose_one]

theorem hsNorm_coisometry_right {a b c : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    [Fintype c] (A : Matrix a b ℂ) (W : Matrix b c ℂ) (hW : W*W.conjTranspose=1) :
    hsNorm (A*W)=hsNorm A := by
  rw [← hsNorm_conjTranspose (A*W),Matrix.conjTranspose_mul]
  rw [hsNorm_isometry_left _ _ (by simpa using hW),hsNorm_conjTranspose]

theorem alice_embedding_reduced {dA dB dC : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (V : Matrix (Fin dC) (Fin dA) ℂ) (hV : V.conjTranspose*V=1) :
    (psi*V.transpose)*(psi*V.transpose).conjTranspose=psi*psi.conjTranspose := by
  rw [Matrix.conjTranspose_mul]
  calc
    _=psi*(V.transpose*(V.transpose).conjTranspose)*psi.conjTranspose := by simp only [Matrix.mul_assoc]
    _=_ := by rw [transpose_isometry_coisometry V hV,Matrix.mul_one]

theorem alice_embedding_expectation {dA dB dC : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (V : Matrix (Fin dC) (Fin dA) ℂ) (P : Mat dC) (A : Mat dA)
    (hP : V.conjTranspose*P*V=A) (Q : Mat dB) :
    expectation (psi*V.transpose) P Q=expectation psi A Q := by
  have ht : V.transpose*P.transpose*(V.transpose).conjTranspose=A.transpose := by
    have h := congrArg Matrix.transpose hP
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
    simpa only [Matrix.transpose_mul,Matrix.mul_assoc] using h
  have he : (psi*V.transpose)*P.transpose*(psi*V.transpose).conjTranspose=psi*A.transpose*psi.conjTranspose := by
    rw [Matrix.conjTranspose_mul]
    calc
      _=psi*(V.transpose*P.transpose*(V.transpose).conjTranspose)*psi.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _=_ := by rw [ht,Matrix.mul_assoc]
  rw [expectation_bob_trace,expectation_bob_trace,he]

/-- The common finite Alice dilation, with invalid outcomes merged into
a valid answer. Every effect is projective on the whole dilation space. -/
def projectiveAliceStrategy {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    Strategy g (Fintype.card (AliceDilationSpace (g:=g) dA)) dB where
  psi := s.psi*(aliceFiniteEmbedding s).transpose
  normalized := by
    change hsNorm (s.psi*(aliceFiniteEmbedding s).transpose)=1
    rw [hsNorm_coisometry_right _ _ (transpose_isometry_coisometry _ (aliceFiniteEmbedding_isometry s))]
    exact s.normalized
  alice := fun i => (aliceFinitePVM s i).effects
  alice_positive := fun i => (aliceFinitePVM s i).effect_posSemidef
  alice_complete := fun i => (aliceFinitePVM s i).sum_eq_one
  alice_valid := aliceFinitePVM_valid s
  bob := s.bob
  bob_positive := s.bob_positive
  bob_complete := s.bob_complete

theorem projectiveAliceStrategy_reduced {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    (projectiveAliceStrategy s).psi*(projectiveAliceStrategy s).psi.conjTranspose=s.psi*s.psi.conjTranspose :=
  alice_embedding_reduced s.psi _ (aliceFiniteEmbedding_isometry s)

theorem projectiveAliceStrategy_pairWin {g : LCS} {dA dB : Nat} (s : Strategy g dA dB)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) :
    pairWin (projectiveAliceStrategy s) i j=pairWin s i j := by
  unfold pairWin
  split
  · apply Finset.sum_congr rfl
    intro a _
    exact alice_embedding_expectation s.psi _ _ _ (aliceFinitePVM_compression s i a) (s.bob j (a j))
  · rfl

theorem projectiveAliceStrategy_win {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    win (projectiveAliceStrategy s)=win s := by
  unfold win
  simp_rw [projectiveAliceStrategy_pairWin]

/-- All measurement reductions used at the start of transfer. The output
is a real strategy, with projective valid Alice measurements and Bob
involutions, on the original Bob Schmidt support. -/
theorem transfer_prepared_strategy {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    ∃ (r dC : Nat) (t : Strategy g dC r) (V : Matrix (Fin dB) (Fin r) ℂ)
      (B : Fin g.system.n → Mat r)
      (P : Fin g.system.equations.length → QIT.ProjectiveMeasurement (Fin g.system.n → Bool) (Fin dC)),
      0<r ∧ r≤dA ∧ r≤dB ∧ (t.psi*t.psi.conjTranspose).PosDef ∧ V.conjTranspose*V=1 ∧
      V*(t.psi*t.psi.conjTranspose)*V.conjTranspose=s.psi*s.psi.conjTranspose ∧
      win s≤win t ∧ (∀ j, IsInvolution (B j)) ∧
      (∀ j b, t.bob j b=CountProof.symmetryProjection (B j) b) ∧
      (∀ i a, t.alice i a=(P i).effects a) := by
  obtain ⟨r,u,V,B,_,hp,hA,hB,hpd,hV,_,hrec,hwin,hBi,he⟩ := support_projectiveBob_reduction s
  let t := projectiveAliceStrategy u
  have ht : t.psi*t.psi.conjTranspose=u.psi*u.psi.conjTranspose := projectiveAliceStrategy_reduced u
  have hw : win s≤win t := by rw [projectiveAliceStrategy_win]; exact hwin
  exact ⟨r,_,t,V,B,aliceFinitePVM u,hp,hA,hB,ht.symm ▸ hpd,hV,ht.symm ▸ hrec,hw,hBi,he,fun _ _ => rfl⟩

end
end Companion.Analytic.TransferProof
