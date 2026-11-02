import Companion.SupportCompression

namespace Companion.Analytic.TransferProof
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

theorem factor_supported {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [Fintype c] [DecidableEq c]
    (psi : Matrix a b ℂ) (V : Matrix a c ℂ) (R : Matrix c c ℂ)
    (hV : V.conjTranspose*V=1) (hr : V*R*V.conjTranspose=psi*psi.conjTranspose) :
    V*(V.conjTranspose*psi)=psi := by
  have hz : (1-V*V.conjTranspose)*(psi*psi.conjTranspose)=0 := by
    rw [← hr,Matrix.sub_mul,Matrix.one_mul]
    have he : (V*V.conjTranspose)*(V*R*V.conjTranspose)=V*R*V.conjTranspose := by
      calc
        _=V*(V.conjTranspose*V)*R*V.conjTranspose := by simp only [Matrix.mul_assoc]
        _=_ := by rw [hV,Matrix.mul_one]
    rw [he,sub_self]
  have h := (Matrix.mul_self_mul_conjTranspose_eq_zero psi (1-V*V.conjTranspose)).mp hz
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc] at h
  exact (sub_eq_zero.mp h).symm

theorem coefficient_pairing_trace {a b : Type*} [Fintype a] [Fintype b]
    (psi A : Matrix a b ℂ) :
    (∑ i, ∑ j, star (psi i j)*A i j)=Matrix.trace (psi.conjTranspose*A) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem expectation_trace {dA dB : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (P : Mat dA) (Q : Mat dB) :
    expectation psi P Q=(Matrix.trace (psi.conjTranspose*((Q*psi)*P.transpose))).re := by
  unfold expectation
  rw [coefficient_pairing_trace]

theorem compressed_expectation {dA dB r : Nat} (psi : Matrix (Fin dB) (Fin dA) ℂ)
    (V : Matrix (Fin dB) (Fin r) ℂ) (hsupp : V*(V.conjTranspose*psi)=psi)
    (P : Mat dA) (Q : Mat dB) :
    expectation (V.conjTranspose*psi) P (V.conjTranspose*Q*V)=expectation psi P Q := by
  have hl : (V.conjTranspose*psi).conjTranspose*V.conjTranspose=psi.conjTranspose := by
    rw [← Matrix.conjTranspose_mul,hsupp]
  have hr : (V.conjTranspose*Q*V)*(V.conjTranspose*psi)=V.conjTranspose*(Q*psi) := by
    calc
      _=V.conjTranspose*Q*(V*(V.conjTranspose*psi)) := by simp only [Matrix.mul_assoc]
      _=_ := by rw [hsupp,Matrix.mul_assoc]
  rw [expectation_trace,expectation_trace,hr]
  congr 2
  calc
    _=((V.conjTranspose*psi).conjTranspose*V.conjTranspose)*((Q*psi)*P.transpose) := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [hl]

/-- Compression of all Bob POVMs to the support leaves every pairwise
winning probability unchanged; Alice's POVMs need no modification. -/
def compressedStrategy {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (r : Nat)
    (V : Matrix (Fin dB) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (hsupp : V*(V.conjTranspose*s.psi)=s.psi) : Strategy g dA r where
  psi := V.conjTranspose*s.psi
  normalized := by
    change hsNorm (V.conjTranspose*s.psi)=1
    rw [← hsNorm_isometry_left V _ hV,hsupp]
    exact s.normalized
  alice := s.alice
  alice_positive := s.alice_positive
  alice_complete := s.alice_complete
  alice_valid := s.alice_valid
  bob := fun j b => V.conjTranspose*s.bob j b*V
  bob_positive := fun j b => by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (s.bob_positive j b).mul_mul_conjTranspose_same V.conjTranspose
  bob_complete := fun j => by
    rw [← Matrix.add_mul,← Matrix.mul_add,s.bob_complete j,Matrix.mul_one,hV]

theorem compressedStrategy_pairWin {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (r : Nat)
    (V : Matrix (Fin dB) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (hsupp : V*(V.conjTranspose*s.psi)=s.psi)
    (i : Fin g.system.equations.length) (j : Fin g.system.n) :
    pairWin (compressedStrategy s r V hV hsupp) i j=pairWin s i j := by
  unfold pairWin
  split
  · apply Finset.sum_congr rfl
    intro a _
    exact compressed_expectation s.psi V hsupp (s.alice i a) (s.bob j (a j))
  · rfl

theorem compressedStrategy_win {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (r : Nat)
    (V : Matrix (Fin dB) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (hsupp : V*(V.conjTranspose*s.psi)=s.psi) :
    win (compressedStrategy s r V hV hsupp)=win s := by
  unfold win
  simp_rw [compressedStrategy_pairWin]

theorem compressedStrategy_reduced {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) (r : Nat)
    (V : Matrix (Fin dB) (Fin r) ℂ) (hV : V.conjTranspose*V=1)
    (R : Mat r) (hr : V*R*V.conjTranspose=s.psi*s.psi.conjTranspose) :
    let t := compressedStrategy s r V hV (factor_supported s.psi V R hV hr)
    t.psi*t.psi.conjTranspose=R := by
  change (V.conjTranspose*s.psi)*(V.conjTranspose*s.psi).conjTranspose=R
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  calc
    _=V.conjTranspose*(s.psi*s.psi.conjTranspose)*V := by simp only [Matrix.mul_assoc]
    _=(V.conjTranspose*V)*R*(V.conjTranspose*V) := by rw [← hr]; simp only [Matrix.mul_assoc]
    _=R := by rw [hV,Matrix.one_mul,Matrix.mul_one]

/-- The full support-compression reduction for the given strategy,
before optimizing Bob's measurements or dilating Alice's measurements. -/
theorem strategy_support_reduction {g : LCS} {dA dB : Nat} (s : Strategy g dA dB) :
    ∃ (r : Nat) (t : Strategy g dA r) (V : Matrix (Fin dB) (Fin r) ℂ),
      r=s.psi.rank ∧ 0<r ∧ r≤dA ∧ r≤dB ∧
      (t.psi*t.psi.conjTranspose).PosDef ∧ V.conjTranspose*V=1 ∧ V*t.psi=s.psi ∧
      V*(t.psi*t.psi.conjTranspose)*V.conjTranspose=s.psi*s.psi.conjTranspose ∧
      (∀ i j, pairWin t i j=pairWin s i j) ∧ win t=win s := by
  obtain ⟨r,rho,V,hr,hp,hA,hB,hpd,hV,hrec,_⟩ := schmidt_support_compression s.psi s.normalized
  let hsupp := factor_supported s.psi V rho.matrix hV hrec
  let t := compressedStrategy s r V hV hsupp
  have ht : t.psi*t.psi.conjTranspose=rho.matrix := compressedStrategy_reduced s r V hV rho.matrix hrec
  exact ⟨r,t,V,hr,hp,hA,hB,ht.symm ▸ hpd,hV,hsupp,ht.symm ▸ hrec,
    compressedStrategy_pairWin s r V hV hsupp,compressedStrategy_win s r V hV hsupp⟩

end
end Companion.Analytic.TransferProof
