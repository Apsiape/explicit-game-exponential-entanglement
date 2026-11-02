import Blueprint.RatesDefinitions
import Blueprint.AConstants
import Mathlib.Data.Nat.Choose.Cast

namespace Blueprint.MixedStates
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 600000

theorem pure_trace_expectation {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (P : Mat a) (Q : Mat b) :
    (pureDensity psi*Matrix.kronecker P Q).trace.re=expectation psi P Q := by
  unfold expectation
  apply congrArg Complex.re
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,pureDensity,Matrix.kronecker_apply,
    Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  dsimp [Matrix.kronecker,Matrix.kroneckerMap]
  ring

theorem ensemble_trace_expectation {a b N : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Fin N → ℝ) (psi : Fin N → Matrix (Fin b) (Fin a) ℂ) (hd : decomposition sigma p psi)
    (P : Mat a) (Q : Mat b) :
    (sigma.matrix*Matrix.kronecker P Q).trace.re=∑ k, p k*expectation (psi k) P Q := by
  rw [hd.2.2.2]
  simp only [Finset.sum_mul,Matrix.smul_mul,Matrix.trace_sum,Matrix.trace_smul,
    Complex.re_sum,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,pure_trace_expectation]

theorem sum_three_cycle {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → ℝ) : (∑ i, ∑ j, ∑ k, f i j k)=∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _=∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _=_ := Finset.sum_comm

theorem ensembles_exist {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) :
    ∃ N p psi, decomposition (N:=N) sigma p psi := by
  let hH := sigma.pos.isHermitian
  let V : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ := hH.eigenvectorUnitary
  have hVU : V.conjTranspose*V=1 := hH.eigenvectorUnitary.property.1
  let e := Fintype.equivFin (Fin a × Fin b)
  let p : Fin (Fintype.card (Fin a × Fin b)) → ℝ := fun k => hH.eigenvalues (e.symm k)
  let psi : Fin (Fintype.card (Fin a × Fin b)) → Matrix (Fin b) (Fin a) ℂ :=
    fun k j i => (V:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (i,j) (e.symm k)
  refine ⟨_,p,psi,?_,?_,?_,?_⟩
  · intro k
    exact sigma.pos.eigenvalues_nonneg _
  · change (∑ k, hH.eigenvalues (e.symm k))=1
    rw [e.symm.sum_comp]
    have hh := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [sigma.trace_eq_one] at hh
    simp only [Complex.one_re,Complex.re_sum] at hh
    convert hh.symm using 1
  · intro k
    have hh := congrArg (fun M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ =>
      (M (e.symm k) (e.symm k)).re) hVU
    have hcol : (∑ i, Complex.normSq ((V:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) i (e.symm k)))=1 := by
      simpa only [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Complex.star_def,
        ←Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Matrix.one_apply_eq,Complex.one_re] using hh
    change Real.sqrt (∑ j, ∑ i, Complex.normSq ((V:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (i,j) (e.symm k)))=1
    have hcol' : (∑ i : Fin a, ∑ j : Fin b, Complex.normSq (V (i,j) (e.symm k)))=1 := by
      simpa only [Fintype.sum_prod_type] using hcol
    rw [Finset.sum_comm,hcol',Real.sqrt_one]
  · have hspec := hH.spectral_theorem
    rw [hspec]
    ext i j
    change ((V:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)*
        Matrix.diagonal (fun k => (hH.eigenvalues k:ℂ))*
        (V:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ).conjTranspose) i j=_
    simp only [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.conjTranspose_apply,
      Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,pureDensity,psi,p]
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    rw [e.symm.sum_comp (fun k => (hH.eigenvalues k:ℂ)*(V i k*star (V j k)))]
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem pure_density_trace_re {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) :
    (pureDensity psi).trace.re=(hs psi)^2 := by
  rw [hs_eq_hsNorm,hsNorm_sq]
  simp only [pureDensity,Matrix.trace,Matrix.diag_apply,Complex.re_sum,hsSquared,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re,Complex.star_def,Complex.normSq_apply]

def pureVector {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    QIT.PureVector (Fin a × Fin b) where
  amp i := psi i.2 i.1
  trace_rankOne_eq_one := by
    change (pureDensity psi).trace=1
    apply Complex.ext
    · simpa only [pure_density_trace_re,hp,one_pow,Complex.one_re]
    · have hh := (QIT.rankOneMatrix_pos (fun i : Fin a × Fin b => psi i.2 i.1)).trace_nonneg.2
      exact hh.symm

theorem pure_density_square {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    pureDensity psi*pureDensity psi=pureDensity psi :=
  (pureVector psi hp).state_matrix_mul_self

theorem pure_density_hermitian {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) :
    (pureDensity psi).conjTranspose=pureDensity psi :=
  QIT.rankOneMatrix_conjTranspose (fun i : Fin a × Fin b => psi i.2 i.1)

theorem pure_density_complement {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    (1-pureDensity psi).PosSemidef := by
  let P := 1-pureDensity psi
  have hH : P.conjTranspose=P := by simp only [P,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,pure_density_hermitian]
  have hP : P*P=P := by
    simp only [P,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,pure_density_square psi hp]
    abel
  have hh := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hH,hP] at hh

theorem countable_trace_linear {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (phi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p phi)
    (A : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    HasSum (fun j => p j*(A*pureDensity (phi j)).trace.re) (A*sigma.matrix).trace.re := by
  have hh := (hd.2.2.2.mul_left A).map (Matrix.traceAddMonoidHom (Fin a × Fin b) ℂ)
    (by exact continuous_id.matrix_trace)
  change HasSum (fun j => (A*((p j:ℂ) • pureDensity (phi j))).trace) (A*sigma.matrix).trace at hh
  simpa only [Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using Complex.hasSum_re hh

theorem trace_mul_psd_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) : 0≤(A*B).trace.re := by
  have hh := hB.mul_mul_conjTranspose_same (QIT.psdSqrt A)
  have ht : ((QIT.psdSqrt A*B)*(QIT.psdSqrt A).conjTranspose).trace=(A*B).trace := by
    rw [QIT.psdSqrt_isHermitian]
    rw [Matrix.trace_mul_cycle,QIT.psdSqrt_mul_self_of_posSemidef hA]
  rw [←ht]
  exact hh.trace_nonneg.1

theorem pure_density_distance {a b : Nat} (psi phi : Matrix (Fin b) (Fin a) ℂ)
    (hp : hs psi=1) (hf : hs phi=1) :
    hsNorm (pureDensity psi-pureDensity phi)^2=2*((1-pureDensity psi)*pureDensity phi).trace.re := by
  rw [hsNorm_sq,hsSquared_trace,Matrix.conjTranspose_sub,pure_density_hermitian,pure_density_hermitian]
  simp only [Matrix.sub_mul,Matrix.mul_sub,pure_density_square psi hp,pure_density_square phi hf,
    Matrix.one_mul,Matrix.trace_sub,Complex.sub_re,pure_density_trace_re,hp,hf,one_pow]
  rw [Matrix.trace_mul_comm (pureDensity phi) (pureDensity psi)]
  ring

theorem pure_ensemble_component {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1)
    (sigma : QIT.State (Fin a × Fin b)) (hs : sigma.matrix=pureDensity psi)
    (p : Nat → ℝ) (phi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p phi)
    (j : Nat) (hj : p j≠0) : pureDensity (phi j)=pureDensity psi := by
  let f := fun k => p k*((1-pureDensity psi)*pureDensity (phi k)).trace.re
  have hf : ∀ k, 0≤f k := by
    intro k
    exact mul_nonneg (hd.1 k) (trace_mul_psd_nonneg _ _ (pure_density_complement psi hp)
      (QIT.rankOneMatrix_pos (fun i : Fin a × Fin b => phi k i.2 i.1)))
  have hfSum : HasSum f 0 := by
    have hh := countable_trace_linear sigma p phi hd (1-pureDensity psi)
    rwa [hs,Matrix.sub_mul,Matrix.one_mul,pure_density_square psi hp,sub_self,Matrix.trace_zero,Complex.zero_re] at hh
  have hj0 : f j=0 := by
    have hh := hfSum.summable.sum_le_tsum {j} (fun k _ => hf k)
    rw [hfSum.tsum_eq] at hh
    simp only [Finset.sum_singleton] at hh
    exact le_antisymm hh (hf j)
  have ht : ((1-pureDensity psi)*pureDensity (phi j)).trace.re=0 := (mul_eq_zero.mp hj0).resolve_left hj
  have hh := pure_density_distance psi (phi j) hp (hd.2.2.1 j)
  rw [ht,mul_zero] at hh
  have hz : hsNorm (pureDensity psi-pureDensity (phi j))=0 := by nlinarith [hsNorm_nonneg (pureDensity psi-pureDensity (phi j))]
  have heq : pureDensity psi-pureDensity (phi j)=0 := by
    letI : NormedAddCommGroup (Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) := Matrix.frobeniusNormedAddCommGroup
    apply norm_eq_zero.mp
    rwa [←hsNorm_eq_frobenius]
  have hz := sub_eq_zero.mp heq
  exact hz.symm

theorem pure_density_gram {a b : Nat} (psi phi : Matrix (Fin b) (Fin a) ℂ)
    (he : pureDensity psi=pureDensity phi) : psi.conjTranspose*psi=phi.conjTranspose*phi := by
  ext i l
  have hh := congrArg (fun M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ => ∑ j, M (l,j) (i,j)) he
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,pureDensity,mul_comm] using hh

theorem countable_singleton {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) (hs : sigma.matrix=pureDensity psi) :
    countableDecomposition sigma (fun j => if j=0 then 1 else 0) (fun _ => psi) := by
  refine ⟨fun j => by dsimp; split <;> positivity,?_,fun _ => hp,?_⟩
  · exact hasSum_ite_eq 0 1
  · simpa only [apply_ite Complex.ofReal,Complex.ofReal_one,Complex.ofReal_zero,ite_smul,one_smul,zero_smul,hs] using
      (hasSum_ite_eq (α:=Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) 0 (pureDensity psi))

theorem gram_entropy_nonnegative {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    0≤entropy (psi.conjTranspose*psi) := by
  have hn : hsNorm psi.conjTranspose=1 := by rw [hsNorm_conjTranspose]; exact hp
  simpa only [State.ofQuAIR,CountProof.factorState,Matrix.conjTranspose_conjTranspose] using
    entropy_nonneg (State.ofQuAIR (CountProof.factorState psi.conjTranspose hn))

theorem gram_entropy_le {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    entropy (psi.conjTranspose*psi)≤log2 a := by
  have hn : hsNorm psi.conjTranspose=1 := by rw [hsNorm_conjTranspose]; exact hp
  simpa only [State.ofQuAIR,CountProof.factorState,Matrix.conjTranspose_conjTranspose,log2] using
    entropy_le_log_dimension (State.ofQuAIR (CountProof.factorState psi.conjTranspose hn))

theorem entropy_transpose {d : Nat} (s : State d) : entropy s.rho.transpose=entropy s.rho := by
  let t : State d := State.ofQuAIR ⟨s.rho.transpose,s.positive.transpose,by rw [Matrix.trace_transpose,s.normalized]⟩
  change entropy t.rho=entropy s.rho
  rw [entropy_eq_quair,entropy_eq_quair,QIT.State.vonNeumann_eq_neg_sum_eigenvalueMultiset,
    QIT.State.vonNeumann_eq_neg_sum_eigenvalueMultiset]
  have hT := t.positive.isHermitian.roots_charpoly_eq_eigenvalues
  have hS := s.positive.isHermitian.roots_charpoly_eq_eigenvalues
  have he : QIT.eigenvalueMultiset t.positive.isHermitian=QIT.eigenvalueMultiset s.positive.isHermitian := by
    have hh := congrArg (fun P : Polynomial ℂ => P.roots.map Complex.re) (Matrix.charpoly_transpose s.rho)
    change t.rho.charpoly.roots.map Complex.re=s.rho.charpoly.roots.map Complex.re at hh
    rw [hT,hS] at hh
    simpa [QIT.eigenvalueMultiset,Multiset.map_map,Function.comp_def] using hh
  change -((QIT.eigenvalueMultiset t.positive.isHermitian).map QIT.xlog2).sum=
    -((QIT.eigenvalueMultiset s.positive.isHermitian).map QIT.xlog2).sum
  rw [he]

theorem gram_entropy_eq {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) :
    entropy (psi.conjTranspose*psi)=entropy (psi*psi.conjTranspose) := by
  let A := State.ofQuAIR (CountProof.factorState psi.transpose (by
    rw [hsNorm_eq_frobenius,Matrix.frobenius_norm_transpose,←hsNorm_eq_frobenius]; exact hp))
  let B := State.ofQuAIR (CountProof.factorState psi hp)
  have hA : (pureVector psi hp).state.marginalA=A.toQuAIR := by
    apply QIT.State.ext
    ext i l
    simp only [QIT.State.marginalA,QIT.partialTraceB,QIT.PureVector.state_matrix,QIT.rankOneMatrix_apply,
      pureVector,A,CountProof.factorState,State.ofQuAIR,State.toQuAIR,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.conjTranspose_conjTranspose,Matrix.transpose_apply]
  have hB : (pureVector psi hp).state.marginalB=B.toQuAIR := by
    apply QIT.State.ext
    ext i l
    simp only [QIT.State.marginalB,QIT.partialTraceA,QIT.PureVector.state_matrix,QIT.rankOneMatrix_apply,
      pureVector,B,CountProof.factorState,State.ofQuAIR,State.toQuAIR,Matrix.mul_apply,Matrix.conjTranspose_apply]
  have hh := QIT.State.pureVector_marginalA_vonNeumann_eq_marginalB (pureVector psi hp)
  rw [hA,hB,←entropy_eq_quair,←entropy_eq_quair] at hh
  have heA : A.rho=(psi.conjTranspose*psi).transpose := by
    ext i l
    simp only [A,CountProof.factorState,State.ofQuAIR,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heA] at hh
  have hAT := entropy_transpose (State.ofQuAIR (CountProof.factorState psi.conjTranspose
    (by rw [hsNorm_conjTranspose]; exact hp)))
  simp only [CountProof.factorState,State.ofQuAIR,Matrix.conjTranspose_conjTranspose] at hAT
  rwa [hAT] at hh

theorem hasSum_nat_fin {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    (N : Nat) (f : Fin N → E) : HasSum (fun j : Nat => if h : j<N then f ⟨j,h⟩ else 0) (∑ j, f j) := by
  let F := fun j : Nat => if h : j<N then f ⟨j,h⟩ else 0
  have hh : HasSum F (∑ j∈Finset.range N, F j) := hasSum_sum_of_ne_finset_zero (by
    intro j hj
    have hnot : ¬j<N := by simpa only [Finset.mem_range] using hj
    exact dif_neg hnot)
  have hsum : (∑ j∈Finset.range N, F j)=∑ j, f j := by
    rw [Finset.sum_range]
    simp only [F,Fin.isLt,↓reduceDIte]
  rwa [hsum] at hh

theorem finite_to_countable {a b N : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Fin N → ℝ) (psi : Fin N → Matrix (Fin b) (Fin a) ℂ) (hd : decomposition sigma p psi) :
    ∃ q phi, countableDecomposition sigma q phi ∧
      (∑' j, q j*entropy ((phi j).conjTranspose*phi j))=∑ j, p j*entropy ((psi j).conjTranspose*psi j) := by
  have hN : N≠0 := by
    intro hh
    subst N
    have hh := hd.2.1
    simpa using hh
  let i0 : Fin N := ⟨0,Nat.pos_of_ne_zero hN⟩
  let q := fun j : Nat => if h : j<N then p ⟨j,h⟩ else 0
  let phi := fun j : Nat => if h : j<N then psi ⟨j,h⟩ else psi i0
  have hterm (j : Nat) : (q j:ℂ) • pureDensity (phi j)=
      if h : j<N then (p ⟨j,h⟩:ℂ) • pureDensity (psi ⟨j,h⟩) else 0 := by
    by_cases hj : j<N <;> simp [q,phi,hj]
  have hcost (j : Nat) : q j*entropy ((phi j).conjTranspose*phi j)=
      if h : j<N then p ⟨j,h⟩*entropy ((psi ⟨j,h⟩).conjTranspose*psi ⟨j,h⟩) else 0 := by
    by_cases hj : j<N <;> simp [q,phi,hj]
  refine ⟨q,phi,⟨?_,?_,?_,?_⟩,?_⟩
  · intro j
    dsimp [q]
    split
    · exact hd.1 _
    · exact le_rfl
  · simpa only [hd.2.1] using hasSum_nat_fin N p
  · intro j
    dsimp [phi]
    split <;> exact hd.2.2.1 _
  · simp_rw [hterm]
    rw [hd.2.2.2]
    exact hasSum_nat_fin N (fun j => (p j:ℂ) • pureDensity (psi j))
  · simp_rw [hcost]
    exact (hasSum_nat_fin N (fun j => p j*entropy ((psi j).conjTranspose*psi j))).tsum_eq

theorem countable_ensembles_exist {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) :
    ∃ p psi, countableDecomposition sigma p psi := by
  obtain ⟨N,p,psi,hd⟩ := ensembles_exist sigma
  obtain ⟨q,phi,hq,_⟩ := finite_to_countable sigma p psi hd
  exact ⟨q,phi,hq⟩

theorem countable_entropy_summable {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (psi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p psi) :
    Summable (fun j => p j*entropy ((psi j).conjTranspose*psi j)) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (hd.1 j) (gram_entropy_nonnegative _ (hd.2.2.1 j)))
    (fun j => mul_le_mul_of_nonneg_left ((gram_entropy_le _ (hd.2.2.1 j)).trans (le_max_left (log2 a) 0)) (hd.1 j))
    (hd.2.1.summable.mul_right (max (log2 a) 0))

theorem finite_cost_bdd {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) :
    BddBelow {v | ∃ N p psi, decomposition (N:=N) sigma p psi ∧
      v=∑ j, p j*entropy ((psi j).conjTranspose*psi j)} := by
  refine ⟨0,?_⟩
  rintro v ⟨N,p,psi,hd,rfl⟩
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hd.1 j) (gram_entropy_nonnegative _ (hd.2.2.1 j)))

theorem countable_cost_bdd {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) :
    BddBelow {v | ∃ p psi, countableDecomposition sigma p psi ∧
      v=∑' j, p j*entropy ((psi j).conjTranspose*psi j)} := by
  refine ⟨0,?_⟩
  rintro v ⟨p,psi,hd,rfl⟩
  exact tsum_nonneg (fun j => mul_nonneg (hd.1 j) (gram_entropy_nonnegative _ (hd.2.2.1 j)))

theorem finite_formation_bound {a b : Nat} {ι : Type} [Fintype ι]
    (sigma : QIT.State (Fin a × Fin b)) (p : ι → ℝ) (psi : ι → Matrix (Fin b) (Fin a) ℂ)
    (hp : ∀ j, 0≤p j) (hm : ∑ j, p j=1) (hn : ∀ j, hs (psi j)=1)
    (hd : sigma.matrix=∑ j, (p j:ℂ) • pureDensity (psi j)) :
    finiteFormation sigma≤∑ j, p j*entropy ((psi j).conjTranspose*psi j) := by
  let e := Fintype.equivFin ι
  have hD : decomposition sigma (fun j => p (e.symm j)) (fun j => psi (e.symm j)) := by
    refine ⟨fun j => hp _,?_,fun j => hn _,?_⟩
    · rwa [e.symm.sum_comp]
    · change sigma.matrix=∑ j, (p (e.symm j):ℂ) • pureDensity (psi (e.symm j))
      rwa [e.symm.sum_comp (fun j => (p j:ℂ) • pureDensity (psi j))]
  have hh := csInf_le (finite_cost_bdd sigma) ⟨_,_,_,hD,rfl⟩
  rwa [e.symm.sum_comp (fun j => p j*entropy ((psi j).conjTranspose*psi j))] at hh

theorem finite_residual_bound {a b N : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Fin N → ℝ) (psi : Fin N → Matrix (Fin b) (Fin a) ℂ)
    (hp : ∀ j, 0≤p j) (hn : ∀ j, hs (psi j)=1)
    (T : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (r : ℝ) (hr : 0≤r)
    (hm : (∑ j, p j)+r=1) (hT : T.PosSemidef) (ht : T.trace=(r:ℂ))
    (hd : sigma.matrix=(∑ j, (p j:ℂ) • pureDensity (psi j))+T) :
    finiteFormation sigma≤(∑ j, p j*entropy ((psi j).conjTranspose*psi j))+r*max (log2 a) 0 := by
  classical
  by_cases hr0 : r=0
  · have htz : T=0 := hT.trace_eq_zero_iff.mp (by simpa only [hr0,Complex.ofReal_zero] using ht)
    have hh := finite_formation_bound sigma p psi hp (by simpa only [hr0,add_zero] using hm) hn
      (by simpa only [htz,add_zero] using hd)
    simpa only [hr0,zero_mul,add_zero] using hh
  have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
  let tau : QIT.State (Fin a × Fin b) := {
    matrix := (r:ℂ)⁻¹ • T
    pos := hT.smul (by exact_mod_cast (inv_nonneg.mpr hr : (0:ℝ)≤r⁻¹))
    trace_eq_one := by rw [Matrix.trace_smul,ht,smul_eq_mul,inv_mul_cancel₀ (by exact_mod_cast hr0 : (r:ℂ)≠0)] }
  obtain ⟨M,q,phi,hq⟩ := ensembles_exist tau
  have htail : (∑ j, (r*q j:ℂ) • pureDensity (phi j))=T := by
    calc
      _=(r:ℂ) • (∑ j, (q j:ℂ) • pureDensity (phi j)) := by
        simp only [Finset.smul_sum,smul_smul,Complex.ofReal_mul]
      _=(r:ℂ) • tau.matrix := congrArg ((r:ℂ) • ·) hq.2.2.2.symm
      _=T := by
        change (r:ℂ) • ((r:ℂ)⁻¹ • T)=T
        rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast hr0 : (r:ℂ)≠0),one_smul]
  let w : Fin N ⊕ Fin M → ℝ := Sum.elim p (fun j => r*q j)
  let v : Fin N ⊕ Fin M → Matrix (Fin b) (Fin a) ℂ := Sum.elim psi phi
  have hw : ∀ j, 0≤w j := by intro j; cases j with
    | inl j => exact hp j
    | inr j => exact mul_nonneg hr (hq.1 j)
  have hmass : (∑ j, w j)=1 := by
    rw [Fintype.sum_sum_type]
    change (∑ j, p j)+(∑ j, r*q j)=1
    rw [←Finset.mul_sum,hq.2.1,mul_one]
    exact hm
  have hnorm : ∀ j, hs (v j)=1 := by intro j; cases j with
    | inl j => exact hn j
    | inr j => exact hq.2.2.1 j
  have hmatrix : sigma.matrix=∑ j, (w j:ℂ) • pureDensity (v j) := by
    rw [Fintype.sum_sum_type]
    simp only [w,v,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_mul]
    rwa [htail]
  have hh := finite_formation_bound sigma w v hw hmass hnorm hmatrix
  rw [Fintype.sum_sum_type] at hh
  change finiteFormation sigma≤(∑ j, p j*entropy ((psi j).conjTranspose*psi j))+
    (∑ j, r*q j*entropy ((phi j).conjTranspose*phi j)) at hh
  have hcost : (∑ j, q j*entropy ((phi j).conjTranspose*phi j))≤max (log2 a) 0 := by
    calc
      _≤∑ j, q j*max (log2 a) 0 := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left ((gram_entropy_le _ (hq.2.2.1 j)).trans (le_max_left _ _)) (hq.1 j))
      _=max (log2 a) 0 := by rw [←Finset.sum_mul,hq.2.1,one_mul]
  have he : (∑ j, r*q j*entropy ((phi j).conjTranspose*phi j))=
      r*(∑ j, q j*entropy ((phi j).conjTranspose*phi j)) := by simp only [Finset.mul_sum,mul_assoc]
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcost hr))

theorem countable_truncation_bound {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (psi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p psi)
    (N : Nat) : finiteFormation sigma≤
      (∑ j∈Finset.range N, p j*entropy ((psi j).conjTranspose*psi j))+
        (1-∑ j∈Finset.range N, p j)*max (log2 a) 0 := by
  let F := fun j => (p j:ℂ) • pureDensity (psi j)
  let T := sigma.matrix-∑ j∈Finset.range N, F j
  let r := 1-∑ j∈Finset.range N, p j
  have hr : 0≤r := by
    have hh := hd.2.1.summable.sum_le_tsum (Finset.range N) (fun j _ => hd.1 j)
    rw [hd.2.1.tsum_eq] at hh
    exact sub_nonneg.mpr hh
  have hprefix : HasSum (fun j => if j<N then F j else 0) (∑ j∈Finset.range N, F j) := by
    simpa only [←Finset.sum_range,dite_eq_ite] using hasSum_nat_fin N (fun j : Fin N => F j)
  have htail : HasSum (fun j => F j-(if j<N then F j else 0)) T := hd.2.2.2.sub hprefix
  have hpos (j : Nat) : (F j-(if j<N then F j else 0)).PosSemidef := by
    by_cases hj : j<N
    · simp only [hj,↓reduceIte,sub_self]
      exact Matrix.PosSemidef.zero
    · simp only [hj,↓reduceIte,sub_zero]
      exact (QIT.rankOneMatrix_pos (fun i : Fin a × Fin b => psi j i.2 i.1)).smul (by exact_mod_cast hd.1 j)
  have hT : T.PosSemidef := by
    apply Matrix.posSemidef_is_closed.mem_of_tendsto htail
    apply Filter.Eventually.of_forall
    intro s
    exact Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg (fun j _ => (hpos j).nonneg))
  have ht : T.trace=(r:ℂ) := by
    have htj (j : Nat) : (pureDensity (psi j)).trace=1 := (pureVector (psi j) (hd.2.2.1 j)).trace_rankOne_eq_one
    simp only [T,r,F,Matrix.trace_sub,Matrix.trace_sum,Matrix.trace_smul,htj,smul_eq_mul,mul_one,
      sigma.trace_eq_one,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_sum]
  have hh := finite_residual_bound sigma (fun j : Fin N => p j) (fun j : Fin N => psi j)
    (fun j => hd.1 j) (fun j => hd.2.2.1 j) T r hr (by rw [←Finset.sum_range]; dsimp [r]; ring)
    hT ht (by rw [←Finset.sum_range (fun j : Nat => (p j:ℂ) • pureDensity (psi j))]; dsimp [T,F]; abel)
  simpa only [←Finset.sum_range (fun j : Nat => p j*entropy ((psi j).conjTranspose*psi j)),r] using hh

theorem countable_cost_ge_finite {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (psi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p psi) :
    finiteFormation sigma≤∑' j, p j*entropy ((psi j).conjTranspose*psi j) := by
  have hmass := hd.2.1.tendsto_sum_nat
  have hcost := (countable_entropy_summable sigma p psi hd).hasSum.tendsto_sum_nat
  have hconst : Filter.Tendsto (fun _ : Nat => (1:ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have hlim := hcost.add ((hconst.sub hmass).mul_const (max (log2 a) 0))
  have hlim' : Filter.Tendsto (fun N =>
      (∑ j∈Finset.range N, p j*entropy ((psi j).conjTranspose*psi j))+
        (1-∑ j∈Finset.range N, p j)*max (log2 a) 0)
      Filter.atTop (nhds (∑' j, p j*entropy ((psi j).conjTranspose*psi j))) := by simpa using hlim
  exact ge_of_tendsto hlim' (Filter.Eventually.of_forall (countable_truncation_bound sigma p psi hd))

theorem finite_countable_equiv {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) :
    finiteFormation sigma=entanglementFormation sigma := by
  apply le_antisymm
  · unfold entanglementFormation
    apply le_csInf
    · obtain ⟨p,psi,hd⟩ := countable_ensembles_exist sigma
      exact ⟨_,p,psi,hd,rfl⟩
    · rintro v ⟨p,psi,hd,rfl⟩
      exact countable_cost_ge_finite sigma p psi hd
  · unfold finiteFormation
    apply le_csInf
    · obtain ⟨N,p,psi,hd⟩ := ensembles_exist sigma
      exact ⟨_,N,p,psi,hd,rfl⟩
    · rintro v ⟨N,p,psi,hd,rfl⟩
      obtain ⟨q,phi,hq,hcost⟩ := finite_to_countable sigma p psi hd
      have hh := csInf_le (countable_cost_bdd sigma) ⟨q,phi,hq,rfl⟩
      rwa [hcost] at hh


theorem formation_nonnegative {a b : Nat} (sigma : QIT.State (Fin a × Fin b)) :
    0≤entanglementFormation sigma := by
  unfold entanglementFormation
  apply Real.sInf_nonneg
  rintro v ⟨p,psi,hd,rfl⟩
  apply tsum_nonneg
  intro j
  apply mul_nonneg (hd.1 j)
  have hn : hsNorm (psi j).conjTranspose=1 := by
    rw [hsNorm_conjTranspose]
    exact hd.2.2.1 j
  have hh := entropy_nonneg (State.ofQuAIR (CountProof.factorState (psi j).conjTranspose hn))
  change 0≤entropy ((psi j).conjTranspose*(psi j).conjTranspose.conjTranspose) at hh
  simpa only [Matrix.conjTranspose_conjTranspose] using hh

theorem formation_pure {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1)
    (sigma : QIT.State (Fin a × Fin b)) (hs : sigma.matrix=pureDensity psi) :
    entanglementFormation sigma=entropy (psi.conjTranspose*psi) := by
  let C := entropy (psi.conjTranspose*psi)
  have hsame (p : Nat → ℝ) (phi : Nat → Matrix (Fin b) (Fin a) ℂ)
      (hd : countableDecomposition sigma p phi) :
      (∑' j, p j*entropy ((phi j).conjTranspose*phi j))=C := by
    have hh (j : Nat) : p j*entropy ((phi j).conjTranspose*phi j)=p j*C := by
      by_cases hj : p j=0
      · simp only [hj,zero_mul]
      · rw [pure_density_gram _ _ (pure_ensemble_component psi hp sigma hs p phi hd j hj)]
    simp_rw [hh]
    exact (by simpa using (hd.2.1.mul_right C).tsum_eq)
  have hset : {v | ∃ p phi, countableDecomposition sigma p phi ∧
      v=∑' j, p j*entropy ((phi j).conjTranspose*phi j)}={C} := by
    ext v
    constructor
    · rintro ⟨p,phi,hd,rfl⟩
      exact Set.mem_singleton_iff.mpr (hsame p phi hd)
    · intro hv
      have hd := countable_singleton sigma psi hp hs
      exact ⟨_,_,hd,(Set.mem_singleton_iff.mp hv).trans (hsame _ _ hd).symm⟩
  unfold entanglementFormation
  rw [hset,csInf_singleton]


theorem mixed_win_linear {a b N : Nat} (g : LCS) (sigma : QIT.State (Fin a × Fin b))
    (p : Fin N → ℝ) (psi : Fin N → Matrix (Fin b) (Fin a) ℂ) (hd : decomposition sigma p psi)
    (m : Measurements g a b) (hm : validMeasurements m) :
    mixedWin sigma m=∑ k, p k*(∑ i, ∑ j, g.pi i j*
      if j.val∈(g.system.equations[i.val]).vars then ∑ x, expectation (psi k) (m.1 i x) (m.2 j (x j)) else 1) := by
  have hpair (i : Fin g.system.equations.length) (j : Fin g.system.n) :
      (if j.val∈(g.system.equations[i.val]).vars then
        ∑ x, (sigma.matrix*Matrix.kronecker (m.1 i x) (m.2 j (x j))).trace.re else 1)=
      ∑ k, p k*(if j.val∈(g.system.equations[i.val]).vars then
        ∑ x, expectation (psi k) (m.1 i x) (m.2 j (x j)) else 1) := by
    by_cases hj : j.val∈(g.system.equations[i.val]).vars
    · simp only [hj,↓reduceIte,ensemble_trace_expectation sigma p psi hd,Finset.mul_sum]
      exact Finset.sum_comm
    · simp only [hj,↓reduceIte,mul_one,hd.2.1]
  unfold mixedWin
  simp_rw [hpair,Finset.mul_sum]
  rw [sum_three_cycle]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mixed_chsh_linear {a b N n : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Fin N → ℝ) (psi : Fin N → Matrix (Fin b) (Fin a) ℂ) (hd : decomposition sigma p psi)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) :
    mixedCHSHBias sigma A B=∑ k, p k*chshBias (psi k) A B := by
  have hpair (i j : Fin n) :
      (sigma.matrix*(Matrix.kronecker (A i) (B i j+B j i)+
        Matrix.kronecker (A j) (B i j-B j i))).trace.re=
        ∑ k, p k*chshPair (psi k) A B i j := by
    simp only [Matrix.mul_add,Matrix.trace_add,Complex.add_re,
      ensemble_trace_expectation sigma p psi hd,←Finset.sum_add_distrib,chshPair,mul_add]
  unfold mixedCHSHBias chshBias
  simp_rw [hpair]
  have hi (i j : Fin n) : (if i<j then ∑ k, p k*chshPair (psi k) A B i j else 0)=
      ∑ k, p k*(if i<j then chshPair (psi k) A B i j else 0) := by
    by_cases hh : i<j <;> simp [hh]
  simp_rw [hi]
  rw [sum_three_cycle]
  simp only [Finset.sum_div,Finset.mul_sum,mul_div_assoc]

theorem markov_half {N : Nat} (p loss : Fin N → ℝ) (eps : ℝ)
    (he : 0<eps) (hp : ∀ k, 0≤p k) (hs : ∑ k, p k=1)
    (hl : ∀ k, 0≤loss k) (ha : (∑ k, p k*loss k)≤eps) :
    (1/2:ℝ)≤∑ k, if loss k≤2*eps then p k else 0 := by
  classical
  have hpart : (∑ k, if loss k≤2*eps then p k else 0)+
      (∑ k, if loss k≤2*eps then 0 else p k)=1 := by
    rw [←Finset.sum_add_distrib]
    convert hs using 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : loss k≤2*eps <;> simp [hk]
  have hb : 2*eps*(∑ k, if loss k≤2*eps then 0 else p k)≤eps := by
    calc
      _=∑ k, 2*eps*(if loss k≤2*eps then 0 else p k) := Finset.mul_sum ..
      _≤∑ k, p k*loss k := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : loss k≤2*eps
        · simp only [hk,↓reduceIte,mul_zero]
          exact mul_nonneg (hp k) (hl k)
        · simp only [hk,↓reduceIte]
          nlinarith [hp k,lt_of_not_ge hk]
      _≤eps := ha
  nlinarith

def measurementStrategy {g : LCS} {a b : Nat} (m : Measurements g a b) (hm : validMeasurements m)
    (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1) : Strategy g a b where
  psi := psi
  normalized := hp
  alice := m.1
  alice_positive := hm.1
  alice_complete := hm.2.1
  alice_valid := hm.2.2.1
  bob := m.2
  bob_positive := hm.2.2.2.1
  bob_complete := hm.2.2.2.2

theorem strategy_win_le_one {g : LCS} {a b : Nat} (s : Strategy g a b) : win s≤1 := by
  calc
    _≤∑ i, ∑ j, g.pi i j*1 := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_left (TransferProof.pairWin_le_one s i j) (g.pi_nonneg i j)))
    _=1 := by simp only [mul_one,g.pi_normalized]

theorem countable_expectation {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (psi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p psi)
    (P : Mat a) (Q : Mat b) :
    HasSum (fun j => p j*expectation (psi j) P Q) (sigma.matrix*Matrix.kronecker P Q).trace.re := by
  have hh := countable_trace_linear sigma p psi hd (Matrix.kronecker P Q)
  have he (phi : Matrix (Fin b) (Fin a) ℂ) :
      (Matrix.kronecker P Q*pureDensity phi).trace.re=expectation phi P Q := by
    rw [Matrix.trace_mul_comm,pure_trace_expectation]
  have ht : (Matrix.kronecker P Q*sigma.matrix).trace.re=(sigma.matrix*Matrix.kronecker P Q).trace.re := by
    rw [Matrix.trace_mul_comm]
  simpa only [he,ht] using hh

theorem countable_strategy_win {g : LCS} {a b : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (psi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p psi)
    (m : Measurements g a b) (hm : validMeasurements m) :
    HasSum (fun k => p k*win (measurementStrategy m hm (psi k) (hd.2.2.1 k))) (mixedWin sigma m) := by
  have hpair (i : Fin g.system.equations.length) (j : Fin g.system.n) :
      HasSum (fun k => p k*pairWin (measurementStrategy m hm (psi k) (hd.2.2.1 k)) i j)
        (if j.val∈(g.system.equations[i.val]).vars then
          ∑ x, (sigma.matrix*Matrix.kronecker (m.1 i x) (m.2 j (x j))).trace.re else 1) := by
    by_cases hj : j.val∈(g.system.equations[i.val]).vars
    · simpa only [pairWin,measurementStrategy,hj,↓reduceIte,Finset.mul_sum] using
        (hasSum_sum (fun x (_ : x∈Finset.univ) => countable_expectation sigma p psi hd (m.1 i x) (m.2 j (x j))))
    · simpa only [pairWin,hj,↓reduceIte,mul_one] using hd.2.1
  have hh := hasSum_sum (fun i (_ : i∈Finset.univ) =>
    hasSum_sum (fun j (_ : j∈Finset.univ) => (hpair i j).mul_left (g.pi i j)))
  simpa only [win,mixedWin,Finset.mul_sum,mul_left_comm] using hh

theorem countable_markov_half (p loss : Nat → ℝ) (eps L : ℝ) (he : 0<eps)
    (hp : ∀ k, 0≤p k) (hs : HasSum p 1) (hl : ∀ k, 0≤loss k)
    (hsLoss : HasSum (fun k => p k*loss k) L) (hL : L≤eps) :
    (1/2:ℝ)≤∑' k, if loss k≤2*eps then p k else 0 := by
  let g := fun k => if loss k≤2*eps then p k else 0
  have hg : Summable g := Summable.of_nonneg_of_le
    (fun k => by dsimp [g]; split; exact hp k; exact le_rfl)
    (fun k => by dsimp [g]; split <;> simp_all only [le_refl]) hs.summable
  have hpoint (k : Nat) : 2*eps*(p k-g k)≤p k*loss k := by
    by_cases hk : loss k≤2*eps
    · simp only [g,hk,↓reduceIte,sub_self,mul_zero]
      exact mul_nonneg (hp k) (hl k)
    · simp only [g,hk,↓reduceIte,sub_zero]
      nlinarith [hp k,lt_of_not_ge hk]
  have hh := ((hs.summable.sub hg).mul_left (2*eps)).tsum_le_tsum hpoint hsLoss.summable
  rw [tsum_mul_left,hs.summable.tsum_sub hg,hs.tsum_eq,hsLoss.tsum_eq] at hh
  change (1/2:ℝ)≤∑' k, g k
  nlinarith

theorem countable_cost_lower (p loss cost : Nat → ℝ) (eps L C : ℝ) (he : 0<eps)
    (hp : ∀ k, 0≤p k) (hs : HasSum p 1) (hl : ∀ k, 0≤loss k)
    (hsLoss : HasSum (fun k => p k*loss k) L) (hL : L≤eps) (hC : 0≤C)
    (hc : ∀ k, 0≤cost k) (hgood : ∀ k, loss k≤2*eps → C≤cost k)
    (hsCost : Summable (fun k => p k*cost k)) :
    C/2≤∑' k, p k*cost k := by
  let g := fun k => if loss k≤2*eps then p k else 0
  have hg : Summable g := Summable.of_nonneg_of_le
    (fun k => by dsimp [g]; split; exact hp k; exact le_rfl)
    (fun k => by dsimp [g]; split <;> simp_all only [le_refl]) hs.summable
  have hm : (1/2:ℝ)≤∑' k, g k := countable_markov_half p loss eps L he hp hs hl hsLoss hL
  have hpoint (k : Nat) : C*g k≤p k*cost k := by
    by_cases hk : loss k≤2*eps
    · change C*(if loss k≤2*eps then p k else 0)≤_
      rw [if_pos hk,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hgood k hk) (hp k)
    · simp only [g,hk,↓reduceIte,mul_zero]
      exact mul_nonneg (hp k) (hc k)
  have hh := (hg.mul_left C).tsum_le_tsum hpoint hsCost
  rw [tsum_mul_left] at hh
  nlinarith

theorem main_from_pure (h : MainPureLower) : MainMixedLower := by
  intro a b sigma m eps hm he hs hw
  have he2 : 0<2*eps := by positivity
  have hs2 : 2*eps≤mainEps := by linarith
  have hhalf : 2*eps≤1/2 := hs2.trans (by
    have hh := zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) (by norm_num : (-5500:ℤ)≤-1)
    simpa [mainEps] using hh)
  have hb := AConstants.bfun_mono_small eps (2*eps) he (by linarith) hhalf
  have hrate : mainRate eps/2≤mainRate (2*eps) := by
    unfold mainRate
    have heq : mainC/(2*eps)*bfun eps=mainC/eps*bfun eps/2 := by ring
    rw [←heq]
    exact mul_le_mul_of_nonneg_left hb (by unfold mainC; positivity)
  unfold entanglementFormation
  apply le_csInf
  · obtain ⟨p,psi,hd⟩ := countable_ensembles_exist sigma
    exact ⟨_,p,psi,hd,rfl⟩
  · rintro v ⟨p,psi,hd,rfl⟩
    let S := fun k => measurementStrategy m hm (psi k) (hd.2.2.1 k)
    let loss := fun k => 1-win (S k)
    let cost := fun k => entropy ((psi k).conjTranspose*psi k)
    have hwin := countable_strategy_win sigma p psi hd m hm
    have hLoss : HasSum (fun k => p k*loss k) (1-mixedWin sigma m) := by
      convert hd.2.1.sub hwin using 1
      funext k
      dsimp [loss,S]
      ring
    have hgood (k : Nat) (hk : loss k≤2*eps) : mainRate (2*eps)≤cost k := by
      have hh := (h a b (S k) (2*eps) he2 hs2 (by dsimp [loss] at hk; linarith)).1
      change mainRate (2*eps)≤entropy (psi k*(psi k).conjTranspose) at hh
      rw [←gram_entropy_eq (psi k) (hd.2.2.1 k)] at hh
      exact hh
    have hh := countable_cost_lower p loss cost eps (1-mixedWin sigma m) (mainRate (2*eps)) he
      hd.1 hd.2.1 (fun k => sub_nonneg.mpr (strategy_win_le_one (S k))) hLoss (by linarith)
      (by unfold mainRate mainC bfun; positivity) (fun k => gram_entropy_nonnegative _ (hd.2.2.1 k))
      hgood (countable_entropy_summable sigma p psi hd)
    linarith

theorem hs_transpose {a b : Nat} (M : Matrix (Fin a) (Fin b) ℂ) : hsNorm M.transpose=hsNorm M := by
  rw [hsNorm_eq_frobenius,Matrix.frobenius_norm_transpose,←hsNorm_eq_frobenius]

open scoped Matrix.Norms.L2Operator in
theorem expectation_hs_upper {a b : Nat} (psi : Matrix (Fin b) (Fin a) ℂ) (hp : hs psi=1)
    (P : Mat a) (Q : Mat b) (hP : contraction P) : expectation psi P Q≤hsNorm (Q*psi) := by
  have he : expectation psi P Q=((psi*P.transpose).conjTranspose*(Q*psi)).trace.re := by
    rw [TransferProof.expectation_trace,Matrix.conjTranspose_mul,hP.1.transpose.eq]
    have hh := congrArg Complex.re (Matrix.trace_mul_comm P.transpose (psi.conjTranspose*(Q*psi)))
    simpa only [Matrix.mul_assoc] using hh.symm
  have hx : hsNorm (psi*P.transpose)≤1 := by
    rw [←hs_transpose (psi*P.transpose),Matrix.transpose_mul,Matrix.transpose_transpose]
    have hh := ReturnProof.operator_mul_hs_bound P psi.transpose
    have hn : hsNorm psi=1 := hp
    rw [hs_transpose,hn,mul_one] at hh
    exact hh.trans hP.2
  rw [he]
  exact (Complex.re_le_norm _).trans ((CountProof.factor_overlap_bound _ _).trans
    ((mul_le_mul_of_nonneg_right hx (hsNorm_nonneg _)).trans_eq (one_mul _)))

theorem hs_parallelogram {a b : Nat} (M N : Matrix (Fin a) (Fin b) ℂ) :
    hsNorm (M+N)^2+hsNorm (M-N)^2=2*(hsNorm M^2+hsNorm N^2) := by
  have hh := parallelogram_law_with_norm ℂ (CountProof.factorVector M) (CountProof.factorVector N)
  have ha : CountProof.factorVector (M+N)=CountProof.factorVector M+CountProof.factorVector N := rfl
  simpa only [←ha,←CountProof.factorVector_sub,CountProof.factorVector_norm] using hh

open scoped Matrix.Norms.L2Operator in
theorem chsh_pair_upper {a b n : Nat} (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) (hv : validCHSH psi A B)
    (i j : Fin n) (hij : i≠j) : chshPair psi A B i j≤2*Real.sqrt 2 := by
  let U := B i j*psi
  let V := B j i*psi
  have hn : hsNorm psi=1 := hv.1
  have hU : hsNorm U≤1 := by
    have hh := ReturnProof.operator_mul_hs_bound (B i j) psi
    rw [hn,mul_one] at hh
    exact hh.trans (hv.2.2 i j hij).2
  have hV : hsNorm V≤1 := by
    have hh := ReturnProof.operator_mul_hs_bound (B j i) psi
    rw [hn,mul_one] at hh
    exact hh.trans (hv.2.2 j i hij.symm).2
  have hp := hs_parallelogram U V
  have hsum : hsNorm (U+V)+hsNorm (U-V)≤2*Real.sqrt 2 := by
    have hUsq : hsNorm U^2≤1 := by nlinarith [hsNorm_nonneg U]
    have hVsq : hsNorm V^2≤1 := by nlinarith [hsNorm_nonneg V]
    nlinarith [sq_nonneg (hsNorm (U+V)-hsNorm (U-V)),hsNorm_nonneg (U+V),hsNorm_nonneg (U-V),
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have h1 := expectation_hs_upper psi hv.1 (A i) (B i j+B j i) (hv.2.1 i)
  have h2 := expectation_hs_upper psi hv.1 (A j) (B i j-B j i) (hv.2.1 j)
  rw [Matrix.add_mul] at h1
  rw [Matrix.sub_mul] at h2
  exact (add_le_add h1 h2).trans hsum

theorem fin_pair_count (n : Nat) : (∑ i : Fin n, ∑ j : Fin n, if i<j then (1:ℝ) else 0)=(n.choose 2:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ,Fin.succ_pos,Fin.succ_lt_succ_iff,Fin.not_lt_zero,
      ↓reduceIte,add_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,zero_add]
    rw [ih,Nat.choose_succ_succ,Nat.choose_one_right,Nat.cast_add]

theorem chsh_bias_upper {a b n : Nat} (hn : 2≤n) (psi : Matrix (Fin b) (Fin a) ℂ)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) (hv : validCHSH psi A B) :
    chshBias psi A B≤optimalBias := by
  have hD : (0:ℝ)<2*n*(n-1:Nat) := by
    have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    have hn1 : (0:ℝ)<(n-1:Nat) := by exact_mod_cast (by omega : 0<n-1)
    positivity
  unfold chshBias
  apply (div_le_iff₀ hD).mpr
  have hh : (∑ i, ∑ j, if i<j then chshPair psi A B i j else 0)≤
      (2*Real.sqrt 2)*(n.choose 2:ℝ) := by
    calc
      _≤∑ i, ∑ j, (2*Real.sqrt 2)*(if i<j then (1:ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i<j
        · simpa only [hij,↓reduceIte,mul_one] using chsh_pair_upper psi A B hv i j (ne_of_lt hij)
        · simp only [hij,↓reduceIte,mul_zero,le_refl]
      _=_ := by simp_rw [←Finset.mul_sum]; rw [fin_pair_count]
  rw [Nat.cast_choose_two] at hh
  have hn1 : ((n-1:Nat):ℝ)=(n:ℝ)-1 := by simp only [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  rw [hn1]
  convert hh using 1 <;> dsimp [optimalBias] <;> ring

theorem countable_chsh_bias {a b n : Nat} (sigma : QIT.State (Fin a × Fin b))
    (p : Nat → ℝ) (psi : Nat → Matrix (Fin b) (Fin a) ℂ) (hd : countableDecomposition sigma p psi)
    (A : Fin n → Mat a) (B : Fin n → Fin n → Mat b) :
    HasSum (fun k => p k*chshBias (psi k) A B) (mixedCHSHBias sigma A B) := by
  have hpair (i j : Fin n) : HasSum (fun k => p k*chshPair (psi k) A B i j)
      (sigma.matrix*(Matrix.kronecker (A i) (B i j+B j i)+Matrix.kronecker (A j) (B i j-B j i))).trace.re := by
    have hh := (countable_expectation sigma p psi hd (A i) (B i j+B j i)).add
      (countable_expectation sigma p psi hd (A j) (B i j-B j i))
    simpa only [chshPair,mul_add,Matrix.mul_add,Matrix.trace_add,Complex.add_re] using hh
  have hterm (i j : Fin n) : HasSum (fun k => if i<j then p k*chshPair (psi k) A B i j else 0)
      (if i<j then (sigma.matrix*(Matrix.kronecker (A i) (B i j+B j i)+Matrix.kronecker (A j) (B i j-B j i))).trace.re else 0) := by
    by_cases hij : i<j
    · simpa only [hij,↓reduceIte] using hpair i j
    · simp only [hij,↓reduceIte]
      exact hasSum_zero
  have hh := (hasSum_sum (fun i (_ : i∈Finset.univ) => hasSum_sum
    (fun j (_ : j∈Finset.univ) => hterm i j))).div_const (2*(n:ℝ)*(n-1:Nat))
  simpa only [chshBias,mixedCHSHBias,←mul_div_assoc,Finset.mul_sum,mul_ite,mul_zero] using hh

theorem chsh_from_pure (h : ELower) : EMixed := by
  intro n a b sigma A B eps hn he hA hB hw
  have hopt : 0<optimalBias := by unfold optimalBias; positivity
  unfold entanglementFormation
  apply le_csInf
  · obtain ⟨p,psi,hd⟩ := countable_ensembles_exist sigma
    exact ⟨_,p,psi,hd,rfl⟩
  · rintro v ⟨p,psi,hd,rfl⟩
    let loss := fun k => 1-chshBias (psi k) A B/optimalBias
    let cost := fun k => entropy ((psi k).conjTranspose*psi k)
    have hv (k : Nat) : validCHSH (psi k) A B := ⟨hd.2.2.1 k,hA,hB⟩
    have hLoss : HasSum (fun k => p k*loss k) (1-mixedCHSHBias sigma A B/optimalBias) := by
      convert hd.2.1.sub ((countable_chsh_bias sigma p psi hd A B).div_const optimalBias) using 1
      funext k
      dsimp [loss]
      ring
    have hl (k : Nat) : 0≤loss k := sub_nonneg.mpr ((div_le_one hopt).mpr
      (chsh_bias_upper (by omega) (psi k) A B (hv k)))
    have hL : 1-mixedCHSHBias sigma A B/optimalBias≤eps := by
      have hh := (le_div_iff₀ hopt).mpr hw
      linarith
    have hg (k : Nat) (hk : loss k≤2*eps) : (chshM n (2*eps):ℝ)/2≤cost k := by
      have hh : (1-2*eps)*optimalBias≤chshBias (psi k) A B := by
        have hh := (le_div_iff₀ hopt).mp (show 1-2*eps≤chshBias (psi k) A B/optimalBias by dsimp [loss] at hk; linarith)
        exact hh
      exact (h n a b (psi k) A B (2*eps) hn (by positivity) (hv k) hh).1
    have hh := countable_cost_lower p loss cost eps _ ((chshM n (2*eps):ℝ)/2) he hd.1 hd.2.1 hl hLoss hL
      (by positivity) (fun k => gram_entropy_nonnegative _ (hd.2.2.1 k)) hg (countable_entropy_summable sigma p psi hd)
    convert hh using 1 <;> ring


end
end Blueprint.MixedStates

-- ROUND-10 DECLARATION AUDIT
#print axioms Blueprint.MixedStates.pure_trace_expectation
#print axioms Blueprint.MixedStates.ensemble_trace_expectation
#print axioms Blueprint.MixedStates.sum_three_cycle
#print axioms Blueprint.MixedStates.ensembles_exist
#print axioms Blueprint.MixedStates.pure_density_trace_re
#print axioms Blueprint.MixedStates.pureVector
#print axioms Blueprint.MixedStates.pure_density_square
#print axioms Blueprint.MixedStates.pure_density_hermitian
#print axioms Blueprint.MixedStates.pure_density_complement
#print axioms Blueprint.MixedStates.countable_trace_linear
#print axioms Blueprint.MixedStates.trace_mul_psd_nonneg
#print axioms Blueprint.MixedStates.pure_density_distance
#print axioms Blueprint.MixedStates.pure_ensemble_component
#print axioms Blueprint.MixedStates.pure_density_gram
#print axioms Blueprint.MixedStates.countable_singleton
#print axioms Blueprint.MixedStates.gram_entropy_nonnegative
#print axioms Blueprint.MixedStates.gram_entropy_le
#print axioms Blueprint.MixedStates.entropy_transpose
#print axioms Blueprint.MixedStates.gram_entropy_eq
#print axioms Blueprint.MixedStates.hasSum_nat_fin
#print axioms Blueprint.MixedStates.finite_to_countable
#print axioms Blueprint.MixedStates.countable_ensembles_exist
#print axioms Blueprint.MixedStates.countable_entropy_summable
#print axioms Blueprint.MixedStates.finite_cost_bdd
#print axioms Blueprint.MixedStates.countable_cost_bdd
#print axioms Blueprint.MixedStates.finite_formation_bound
#print axioms Blueprint.MixedStates.finite_residual_bound
#print axioms Blueprint.MixedStates.countable_truncation_bound
#print axioms Blueprint.MixedStates.countable_cost_ge_finite
#print axioms Blueprint.MixedStates.finite_countable_equiv
#print axioms Blueprint.MixedStates.formation_nonnegative
#print axioms Blueprint.MixedStates.formation_pure
#print axioms Blueprint.MixedStates.mixed_win_linear
#print axioms Blueprint.MixedStates.mixed_chsh_linear
#print axioms Blueprint.MixedStates.markov_half
#print axioms Blueprint.MixedStates.measurementStrategy
#print axioms Blueprint.MixedStates.strategy_win_le_one
#print axioms Blueprint.MixedStates.countable_expectation
#print axioms Blueprint.MixedStates.countable_strategy_win
#print axioms Blueprint.MixedStates.countable_markov_half
#print axioms Blueprint.MixedStates.countable_cost_lower
#print axioms Blueprint.MixedStates.main_from_pure
#print axioms Blueprint.MixedStates.hs_transpose
#print axioms Blueprint.MixedStates.expectation_hs_upper
#print axioms Blueprint.MixedStates.hs_parallelogram
#print axioms Blueprint.MixedStates.chsh_pair_upper
#print axioms Blueprint.MixedStates.fin_pair_count
#print axioms Blueprint.MixedStates.chsh_bias_upper
#print axioms Blueprint.MixedStates.countable_chsh_bias
#print axioms Blueprint.MixedStates.chsh_from_pure
