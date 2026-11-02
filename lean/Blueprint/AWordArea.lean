import Blueprint.Definitions
import Blueprint.A.ConjugatorLengths
import Companion.Areas

namespace Blueprint.AWordArea
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

theorem adjoint_commutator {d : Nat} (U xi : Mat d) (hU : IsUnitary U) :
    hs (comm U.conjTranspose xi)=hs (comm U xi) := by
  have he : comm U.conjTranspose xi= -(U.conjTranspose*comm U xi*U.conjTranspose) := by
    simp only [Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,←Matrix.mul_assoc,hU.1,Matrix.one_mul]
    rw [Matrix.mul_assoc (U.conjTranspose*xi) U U.conjTranspose,hU.2,Matrix.mul_one]
    abel
  rw [he,hs_eq_hsNorm,hs_eq_hsNorm]
  rw [CountProof.hs_neg,
    hsNorm_unitary_right _ _ (by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1),
    hsNorm_unitary_left _ _ (by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2)]

theorem word_commutator {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j))
    (xi : Mat d) (ec : ℝ) (hc : ∀ j, hs (comm (U j) xi)≤ec) (w : Word) :
    hs (comm (wordEval U w) xi)≤w.length*ec := by
  let f := fun a : Nat × Bool => if a.2 then U a.1 else (U a.1).conjTranspose
  have hf : ∀ V∈w.map f, IsUnitary V := by
    intro V hV
    obtain ⟨⟨j,b⟩,_,rfl⟩ := List.mem_map.mp hV
    cases b
    · exact ReturnProof.unitary_adjoint _ (hU j)
    · exact hU j
  have hcf : ∀ V∈w.map f, hsNorm (comm V xi)≤ec := by
    intro V hV
    obtain ⟨⟨j,b⟩,_,rfl⟩ := List.mem_map.mp hV
    cases b
    · change hsNorm (comm (U j).conjTranspose xi)≤ec
      rw [←hs_eq_hsNorm,adjoint_commutator _ _ (hU j)]
      exact hc j
    · exact (by simpa only [f,↓reduceIte,hs_eq_hsNorm] using hc j)
  simpa only [wordEval,hs_eq_hsNorm,List.length_map] using
    ReturnProof.unitary_list_commutator_bound (w.map f) xi ec hf hcf

theorem conjugation {d : Nat} (U G xi : Mat d) (hU : IsUnitary U) (hG : IsUnitary G) :
    hs ((G*U*G.conjTranspose-1)*xi)≤hs ((U-1)*xi)+2*hs (comm G xi) := by
  have he : (G*U*G.conjTranspose-1)*xi=G*((U-1)*G.conjTranspose*xi) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,←Matrix.mul_assoc,hG.2]
  rw [he,hs_eq_hsNorm,hsNorm_unitary_left _ _ hG.1]
  have h := ReturnProof.unitary_difference_right_transport U 1 G.conjTranspose xi hU
    (by simp [IsUnitary]) (ReturnProof.unitary_adjoint _ hG)
  simpa only [←hs_eq_hsNorm,adjoint_commutator _ _ hG] using h

theorem inverse_defect {d : Nat} (U xi : Mat d) (hU : IsUnitary U) :
    hs ((U.conjTranspose-1)*xi)=hs ((U-1)*xi) := by
  have he : (U.conjTranspose-1)*xi= -(U.conjTranspose*((U-1)*xi)) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,←Matrix.mul_assoc,hU.1]
    abel
  rw [he,hs_eq_hsNorm,hs_eq_hsNorm,CountProof.hs_neg,
    hsNorm_unitary_left _ _ (by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2)]

theorem product_defect {d : Nat} (U V xi : Mat d) (hU : IsUnitary U) :
    hs ((U*V-1)*xi)≤hs ((U-1)*xi)+hs ((V-1)*xi) := by
  have he : (U*V-1)*xi=U*((V-1)*xi)+(U-1)*xi := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
    abel
  rw [he]
  have h := hsNorm_add_le (U*((V-1)*xi)) ((U-1)*xi)
  rw [hsNorm_unitary_left _ _ hU.1] at h
  simpa only [hs_eq_hsNorm,add_comm] using h

theorem factor_eval {d : Nat} (rfn : RelKey → Option Word) (U : Nat → Mat d)
    (hU : ∀ j, IsUnitary (U j)) (f : Factor) (r : Word) (hk : rfn f.key=some r) :
    wordEval U (factorWordWith rfn f)=wordEval U f.conjugator*
      (if f.positive then wordEval U r else (wordEval U r).conjTranspose)*
        (wordEval U f.conjugator).conjTranspose := by
  cases hb : f.positive <;>
    simp only [←assignmentHom_word U hU,factorWordWith,hk,Option.getD_some,hb,
      Bool.false_eq_true,↓reduceIte,←FreeGroup.mul_mk,←FreeGroup.inv_mk,map_mul,map_inv,Submonoid.coe_mul] <;> rfl

theorem charged_area {d : Nat} (rfn : RelKey → Option Word) (U : Nat → Mat d)
    (hU : ∀ j, IsUnitary (U j)) (xi : Mat d) (e ec : ℝ) (w : Word) (fs : List Factor)
    (hv : ∀ f∈fs, (rfn f.key).isSome=true) (hw : FreeGroup.mk (expandWith rfn fs)=FreeGroup.mk w)
    (hr : ∀ k r, rfn k=some r → hs ((wordEval U r-1)*xi)≤e)
    (hc : ∀ j, hs (comm (U j) xi)≤ec) :
    hs ((wordEval U w-1)*xi)≤(fs.map (fun f => e+2*f.conjugator.length*ec)).sum := by
  have hf (f : Factor) (hmem : f∈fs) :
      hs ((wordEval U (factorWordWith rfn f)-1)*xi)≤e+2*f.conjugator.length*ec := by
    cases hk : rfn f.key with
    | none => have hh := hv f hmem; simp [hk] at hh
    | some r =>
      have hr' := hr f.key r hk
      have hc' := word_commutator U hU xi ec hc f.conjugator
      have hG := wordEval_unitary U hU f.conjugator
      have hR := wordEval_unitary U hU r
      rw [factor_eval rfn U hU f r hk]
      cases hb : f.positive
      · simp only [hb,Bool.false_eq_true,↓reduceIte]
        have hh := conjugation (wordEval U r).conjTranspose (wordEval U f.conjugator) xi
          (ReturnProof.unitary_adjoint _ hR) hG
        rw [inverse_defect _ _ hR] at hh
        nlinarith
      · simp only [hb,↓reduceIte]
        have hh := conjugation (wordEval U r) (wordEval U f.conjugator) xi hR hG
        nlinarith
  let F := fun f => wordEval U (factorWordWith rfn f)
  have hprod : ∀ xs : List Factor, (∀ f∈xs, f∈fs) →
      hs (((xs.map F).prod-1)*xi)≤(xs.map (fun f => e+2*f.conjugator.length*ec)).sum := by
    intro xs
    induction xs with
    | nil => intro _; simp [hs]
    | cons f xs ih =>
      intro hx
      have hh := product_defect (F f) (xs.map F).prod xi (wordEval_unitary U hU _)
      have ht := ih (fun g hg => hx g (by simp [hg]))
      have hhead := hf f (hx f (by simp))
      simpa only [List.map_cons,List.prod_cons,List.sum_cons] using
        hh.trans (add_le_add hhead ht)
  have heval : wordEval U w=(fs.map F).prod := by
    rw [←assignmentHom_word U hU w,←hw,mk_expandWith,map_list_prod]
    simp only [List.map_map,Function.comp_def]
    generalize fs=xs
    induction xs with
    | nil => rfl
    | cons f xs ih => simpa only [List.map_cons,List.prod_cons,Submonoid.coe_mul,
        assignmentHom_word] using congrArg (fun M => F f*M) ih
  rw [heval]
  exact hprod fs (fun _ h => h)

theorem word_commutator_on {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j))
    (xi : Mat d) (ec : ℝ) (w : Word) (hc : ∀ a∈w, hs (comm (U a.1) xi)≤ec) :
    hs (comm (wordEval U w) xi)≤w.length*ec := by
  let f := fun a : Nat × Bool => if a.2 then U a.1 else (U a.1).conjTranspose
  have hf : ∀ V∈w.map f, IsUnitary V := by
    intro V hV
    obtain ⟨⟨j,b⟩,_,rfl⟩ := List.mem_map.mp hV
    cases b
    · exact ReturnProof.unitary_adjoint _ (hU j)
    · exact hU j
  have hcf : ∀ V∈w.map f, hsNorm (comm V xi)≤ec := by
    intro V hV
    obtain ⟨⟨j,b⟩,ha,rfl⟩ := List.mem_map.mp hV
    have hh := hc (j,b) ha
    cases b
    · change hsNorm (comm (U j).conjTranspose xi)≤ec
      rw [←hs_eq_hsNorm,adjoint_commutator _ _ (hU j)]
      exact hh
    · exact hh
  simpa only [wordEval,hs_eq_hsNorm,List.length_map] using
    ReturnProof.unitary_list_commutator_bound (w.map f) xi ec hf hcf

theorem word_eval_substitution {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j))
    (images : Nat → Word) (w : Word) :
    wordEval (fun j => wordEval U (images j)) w=wordEval U (substituteWords images w) := by
  let hV := fun j => wordEval_unitary U hU (images j)
  have hh : assignmentHom (fun j => wordEval U (images j)) hV=
      (assignmentHom U hU).comp (FreeGroup.lift (fun j => FreeGroup.mk (images j))) := by
    apply FreeGroup.ext_hom
    intro j
    apply Subtype.ext
    simp only [assignmentHom,FreeGroup.lift_apply_of,MonoidHom.comp_apply,asUnitary]
    exact (assignmentHom_word U hU (images j)).symm
  rw [←assignmentHom_word _ hV,hh,MonoidHom.comp_apply,←mk_substituteWords,assignmentHom_word]

def factorCharge (fs : List Factor) : Nat := (fs.map (fun f => 1+2*f.conjugator.length)).sum

theorem factor_charge_scale (fs : List Factor) (e : ℝ) :
    (fs.map (fun f => e+2*f.conjugator.length*e)).sum=factorCharge fs*e := by
  induction fs with
  | nil => simp [factorCharge]
  | cons f fs ih =>
    simp only [List.map_cons,List.sum_cons,factorCharge,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat,Nat.cast_one] at *
    rw [ih]
    ring

theorem charged_area_local {d : Nat} (rfn : RelKey → Option Word) (U : Nat → Mat d)
    (hU : ∀ j, IsUnitary (U j)) (xi : Mat d) (e ec : ℝ) (w : Word) (fs : List Factor)
    (hv : ∀ f∈fs, (rfn f.key).isSome=true) (hw : FreeGroup.mk (expandWith rfn fs)=FreeGroup.mk w)
    (hr : ∀ k r, rfn k=some r → hs ((wordEval U r-1)*xi)≤e)
    (hc : ∀ f∈fs, hs (comm (wordEval U f.conjugator) xi)≤f.conjugator.length*ec) :
    hs ((wordEval U w-1)*xi)≤(fs.map (fun f => e+2*f.conjugator.length*ec)).sum := by
  have hf (f : Factor) (hmem : f∈fs) :
      hs ((wordEval U (factorWordWith rfn f)-1)*xi)≤e+2*f.conjugator.length*ec := by
    cases hk : rfn f.key with
    | none => have hh := hv f hmem; simp [hk] at hh
    | some r =>
      have hr' := hr f.key r hk
      have hc' := hc f hmem
      have hG := wordEval_unitary U hU f.conjugator
      have hR := wordEval_unitary U hU r
      rw [factor_eval rfn U hU f r hk]
      cases hb : f.positive
      · simp only [hb,Bool.false_eq_true,↓reduceIte]
        have hh := conjugation (wordEval U r).conjTranspose (wordEval U f.conjugator) xi
          (ReturnProof.unitary_adjoint _ hR) hG
        rw [inverse_defect _ _ hR] at hh
        nlinarith
      · simp only [hb,↓reduceIte]
        have hh := conjugation (wordEval U r) (wordEval U f.conjugator) xi hR hG
        nlinarith
  let F := fun f => wordEval U (factorWordWith rfn f)
  have hprod : ∀ xs : List Factor, (∀ f∈xs, f∈fs) →
      hs (((xs.map F).prod-1)*xi)≤(xs.map (fun f => e+2*f.conjugator.length*ec)).sum := by
    intro xs
    induction xs with
    | nil => intro _; simp [hs]
    | cons f xs ih =>
      intro hx
      have hh := product_defect (F f) (xs.map F).prod xi (wordEval_unitary U hU _)
      have ht := ih (fun g hg => hx g (by simp [hg]))
      have hhead := hf f (hx f (by simp))
      simpa only [List.map_cons,List.prod_cons,List.sum_cons] using
        hh.trans (add_le_add hhead ht)
  have heval : wordEval U w=(fs.map F).prod := by
    rw [←assignmentHom_word U hU w,←hw,mk_expandWith,map_list_prod]
    simp only [List.map_map,Function.comp_def]
    generalize fs=xs
    induction xs with
    | nil => rfl
    | cons f xs ih => simpa only [List.map_cons,List.prod_cons,Submonoid.coe_mul,
        assignmentHom_word] using congrArg (fun M => F f*M) ih
  rw [heval]
  exact hprod fs (fun _ h => h)

theorem checked_weighted_bound {d : Nat} (rfn : RelKey → Option Word) (U : Nat → Mat d)
    (hU : ∀ j, IsUnitary (U j)) (xi : Mat d) (e : ℝ) (w : Word) (fs : List Factor) (k : Nat)
    (hcheck : checkWith rfn w fs k=true)
    (hr : ∀ key r, rfn key=some r → hs ((wordEval U r-1)*xi)≤e)
    (hc : ∀ f∈fs, ∀ a∈f.conjugator, hs (comm (U a.1) xi)≤e) :
    hs ((wordEval U w-1)*xi)≤factorCharge fs*e := by
  simp only [checkWith,Bool.and_eq_true,decide_eq_true_eq] at hcheck
  have hh := charged_area_local rfn U hU xi e e w fs (List.all_eq_true.mp hcheck.1.2)
    (FreeGroup.reduce.exact hcheck.2) hr
    (fun f hf => word_commutator_on U hU xi e f.conjugator (hc f hf))
  rwa [factor_charge_scale] at hh

def pauliCertificate (i : Fin 27) : List Factor :=
  ([derivationCertificate01, derivationCertificate02, derivationCertificate03, derivationCertificate04, derivationCertificate05, derivationCertificate06, derivationCertificate07, derivationCertificate08, derivationCertificate09, derivationCertificate10, derivationCertificate11, derivationCertificate12, derivationCertificate13, derivationCertificate14, derivationCertificate15, derivationCertificate16, derivationCertificate17, derivationCertificate18, derivationCertificate19, derivationCertificate20, derivationCertificate21, derivationCertificate22, derivationCertificate23, derivationCertificate24, derivationCertificate25, derivationCertificate26, derivationCertificate27]:List (List Factor)).get i

theorem pauli_certificate_checked (i : Fin 27) :
    checkWith (presentationRelator inputPresentation) (derivationTargets.get i) (pauliCertificate i) 60=true := by
  fin_cases i
  · exact derivationCheck01
  · exact derivationCheck02
  · exact derivationCheck03
  · exact derivationCheck04
  · exact derivationCheck05
  · exact derivationCheck06
  · exact derivationCheck07
  · exact derivationCheck08
  · exact derivationCheck09
  · exact derivationCheck10
  · exact derivationCheck11
  · exact derivationCheck12
  · exact derivationCheck13
  · exact derivationCheck14
  · exact derivationCheck15
  · exact derivationCheck16
  · exact derivationCheck17
  · exact derivationCheck18
  · exact derivationCheck19
  · exact derivationCheck20
  · exact derivationCheck21
  · exact derivationCheck22
  · exact derivationCheck23
  · exact derivationCheck24
  · exact derivationCheck25
  · exact derivationCheck26
  · exact derivationCheck27

theorem pauli_certificate_data : ∀ i : Fin 27, factorCharge (pauliCertificate i)≤36780 ∧
    (pauliCertificate i).all (fun f => f.conjugator.all (fun a => decide (1≤a.1 ∧ a.1≤27)))=true := by
  decide +kernel

def thetaImages (j : Nat) : Word := thetaLetter (j,true)

theorem theta_substitution (w : Word) : thetaWord w=substituteWords thetaImages w := by
  unfold thetaWord substituteWords
  apply congrArg (fun f : Nat × Bool → Word => w.flatMap f)
  funext a
  rcases a with ⟨j,b⟩
  cases b <;> rfl

theorem pauli_word_bound {d : Nat} (U : Nat → Mat d) (st : State d) (e : ℝ)
    (he : 0≤e) (hm : presentationModel U st e) (w : Word) (hw : w∈pauliRelators) :
    hs ((wordEval U (thetaWord w)-1)*st.xi)≤36780*e := by
  have ht : thetaWord w∈derivationTargets := by
    rw [derivations_match]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ht
  have hh := checked_weighted_bound (presentationRelator inputPresentation) U hm.1 st.xi e
    (derivationTargets.get i) (pauliCertificate i) 60 (pauli_certificate_checked i) hm.2.1
    (by
      intro f hf a ha
      have hd := List.all_eq_true.mp (pauli_certificate_data i).2 f hf
      have hb := of_decide_eq_true (List.all_eq_true.mp hd a ha)
      exact hm.2.2 a.1 hb.1 hb.2)
  rw [hi] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (pauli_certificate_data i).1) he)

def numericCertificate (i : Fin 120) : List Factor :=
  ([certificate000, certificate001, certificate002, certificate003, certificate004, certificate005, certificate006, certificate007, certificate008, certificate009, certificate010, certificate011, certificate012, certificate013, certificate014, certificate015, certificate016, certificate017, certificate018, certificate019, certificate020, certificate021, certificate022, certificate023, certificate024, certificate025, certificate026, certificate027, certificate028, certificate029, certificate030, certificate031, certificate032, certificate033, certificate034, certificate035, certificate036, certificate037, certificate038, certificate039, certificate040, certificate041, certificate042, certificate043, certificate044, certificate045, certificate046, certificate047, certificate048, certificate049, certificate050, certificate051, certificate052, certificate053, certificate054, certificate055, certificate056, certificate057, certificate058, certificate059, certificate060, certificate061, certificate062, certificate063, certificate064, certificate065, certificate066, certificate067, certificate068, certificate069, certificate070, certificate071, certificate072, certificate073, certificate074, certificate075, certificate076, certificate077, certificate078, certificate079, certificate080, certificate081, certificate082, certificate083, certificate084, certificate085, certificate086, certificate087, certificate088, certificate089, certificate090, certificate091, certificate092, certificate093, certificate094, certificate095, certificate096, certificate097, certificate098, certificate099, certificate100, certificate101, certificate102, certificate103, certificate104, certificate105, certificate106, certificate107, certificate108, certificate109, certificate110, certificate111, certificate112, certificate113, certificate114, certificate115, certificate116, certificate117, certificate118, certificate119]:List (List Factor)).get i

theorem numeric_certificate_checked (i : Fin 120) :
    check suppliedGame (presentationTargets.get i) (numericCertificate i) 42=true := by
  fin_cases i
  · exact checked000
  · exact checked001
  · exact checked002
  · exact checked003
  · exact checked004
  · exact checked005
  · exact checked006
  · exact checked007
  · exact checked008
  · exact checked009
  · exact checked010
  · exact checked011
  · exact checked012
  · exact checked013
  · exact checked014
  · exact checked015
  · exact checked016
  · exact checked017
  · exact checked018
  · exact checked019
  · exact checked020
  · exact checked021
  · exact checked022
  · exact checked023
  · exact checked024
  · exact checked025
  · exact checked026
  · exact checked027
  · exact checked028
  · exact checked029
  · exact checked030
  · exact checked031
  · exact checked032
  · exact checked033
  · exact checked034
  · exact checked035
  · exact checked036
  · exact checked037
  · exact checked038
  · exact checked039
  · exact checked040
  · exact checked041
  · exact checked042
  · exact checked043
  · exact checked044
  · exact checked045
  · exact checked046
  · exact checked047
  · exact checked048
  · exact checked049
  · exact checked050
  · exact checked051
  · exact checked052
  · exact checked053
  · exact checked054
  · exact checked055
  · exact checked056
  · exact checked057
  · exact checked058
  · exact checked059
  · exact checked060
  · exact checked061
  · exact checked062
  · exact checked063
  · exact checked064
  · exact checked065
  · exact checked066
  · exact checked067
  · exact checked068
  · exact checked069
  · exact checked070
  · exact checked071
  · exact checked072
  · exact checked073
  · exact checked074
  · exact checked075
  · exact checked076
  · exact checked077
  · exact checked078
  · exact checked079
  · exact checked080
  · exact checked081
  · exact checked082
  · exact checked083
  · exact checked084
  · exact checked085
  · exact checked086
  · exact checked087
  · exact checked088
  · exact checked089
  · exact checked090
  · exact checked091
  · exact checked092
  · exact checked093
  · exact checked094
  · exact checked095
  · exact checked096
  · exact checked097
  · exact checked098
  · exact checked099
  · exact checked100
  · exact checked101
  · exact checked102
  · exact checked103
  · exact checked104
  · exact checked105
  · exact checked106
  · exact checked107
  · exact checked108
  · exact checked109
  · exact checked110
  · exact checked111
  · exact checked112
  · exact checked113
  · exact checked114
  · exact checked115
  · exact checked116
  · exact checked117
  · exact checked118
  · exact checked119

theorem numeric_certificate_data : ∀ i : Fin 120, factorCharge (numericCertificate i)≤14826 ∧
    (numericCertificate i).all (fun f => f.conjugator.all (fun a => decide (1≤a.1 ∧ a.1≤suppliedGame.n+1)))=true := by
  decide +kernel

theorem numeric_word_bound {d : Nat} (e : ℝ) (he : 0≤e) (m : Model MainProof.concreteLCS d e)
    (w : Word) (hw : w∈substitutedRelators inputPresentation) :
    hs ((wordEval m.U w-1)*m.state.xi)≤cPsi*e := by
  rw [←presentationTargets_match] at hw
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hw
  have hh := checked_weighted_bound (relator suppliedGame) m.U m.unitary m.state.xi e
    (presentationTargets.get i) (numericCertificate i) 42 (numeric_certificate_checked i) m.relators
    (by
      intro f hf a ha
      have hd := List.all_eq_true.mp (numeric_certificate_data i).2 f hf
      have hb := of_decide_eq_true (List.all_eq_true.mp hd a ha)
      exact m.state_commutators a.1 hb.1 hb.2)
  rw [hi] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by
    change (factorCharge (numericCertificate i):ℝ)≤14826
    exact_mod_cast (numeric_certificate_data i).1) he)

def visibilityCertificate : List Factor := [⟨.conjugacy 75,true,[(4,true)]⟩,
  ⟨.equation 4,true,[]⟩,⟨.square 19,false,[]⟩]

theorem visibility_certificate_checked : checkWith (presentationRelator inputPresentation)
    (lampJ.map (fun a => (a.1-1,a.2))++[(20,false)]) visibilityCertificate 3=true := by
  decide +kernel

/-- state.tex, lem:conjugator-length; no hypothesis of bounded conjugators. -/
theorem short_conjugators (hlit : Published.ConjugatorLengths)
    (rfn : RelKey → Option Word) (K k : Nat) (w : Word)
    (hr : ∀ a r, rfn a=some r → r.length≤K) (ha : HasAreaWith rfn w k) :
    ∃ fs : List Factor, fs.length≤k ∧ (∀ f∈fs, (rfn f.key).isSome=true) ∧
      FreeGroup.mk (expandWith rfn fs)=FreeGroup.mk w ∧
      ∀ f∈fs, f.conjugator.length≤w.length+k*K :=
  AWordAreaProof.short_conjugators_of_finite hlit rfn K k w hr ha

theorem model_pullback {d : Nat} (e : ℝ) (he : 0≤e) (m : Model MainProof.concreteLCS d e)
    (hJ : m.U (suppliedGame.n+1)=-1) :
    ∃ U : Nat → Mat d, presentationModel U m.state (cPsi*e) ∧
      1-cPsi*e≤hs ((U (inputPresentation.distinguished+1)-1)*m.state.xi) := by
  let images : Nat → Word := fun j => if j=27 then [(27,true),(28,true)] else [(j,true)]
  let U : Nat → Mat d := fun j => wordEval m.U (images j)
  have hU : ∀ j, IsUnitary (U j) := fun j => wordEval_unitary m.U m.unitary _
  have hwords : substitutedRelators inputPresentation=
      (presentationWords inputPresentation).map (substituteWords images) := by decide +kernel
  have hm : presentationModel U m.state (cPsi*e) := by
    refine ⟨hU,?_,?_⟩
    · intro k r hr
      rw [word_eval_substitution m.U m.unitary images r]
      apply numeric_word_bound e he m
      rw [hwords]
      exact List.mem_map.mpr ⟨r,presentationRelator_mem hr,rfl⟩
    · intro j hj1 hj27
      change hs (comm (wordEval m.U (images j)) m.state.xi)≤cPsi*e
      have hlen : (images j).length≤2 := by dsimp [images]; split <;> simp
      have hsupp : ∀ a∈images j, 1≤a.1 ∧ a.1≤suppliedGame.n+1 := by
        intro a ha
        dsimp [images] at ha
        split at ha
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl <;> constructor <;> decide +kernel
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          subst a
          exact ⟨hj1,hj27.trans (by decide)⟩
      have hc := word_commutator_on m.U m.unitary m.state.xi e (images j)
        (fun a ha => m.state_commutators a.1 (hsupp a ha).1 (hsupp a ha).2)
      exact hc.trans (mul_le_mul_of_nonneg_right (by
        change ((images j).length:ℝ)≤14826
        exact_mod_cast hlen.trans (by decide : 2≤14826)) he)
  refine ⟨U,hm,?_⟩
  have hsupp : certificate120.all (fun f => f.conjugator.all
      (fun a => decide (1≤a.1 ∧ a.1≤suppliedGame.n+1)))=true := by decide +kernel
  have hcharge : factorCharge certificate120≤29650 := by decide +kernel
  have hc := checked_weighted_bound (relator suppliedGame) m.U m.unitary m.state.xi e
    target120 certificate120 42 checked120 m.relators (by
      intro f hf a ha
      have hb := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hsupp f hf) a ha)
      exact m.state_commutators a.1 hb.1 hb.2)
  have hc' : hs ((wordEval m.U target120-1)*m.state.xi)≤29650*e :=
    hc.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcharge) he)
  let A := m.U 20
  let T := m.U 39
  let R := A*T*A.conjTranspose*T.conjTranspose
  have hA : IsUnitary A := m.unitary _
  have hT : IsUnitary T := m.unitary _
  have hRplus : hs ((R+1)*m.state.xi)≤29650*e := by
    have ht : wordEval m.U target120= -R := by
      rw [target120_match]
      change wordEval m.U [(20,true),(39,true),(20,false),(39,false),(suppliedGame.n+1,true)]= -R
      simp only [wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
        Bool.false_eq_true,↓reduceIte,Matrix.mul_one,hJ,Matrix.mul_neg,Matrix.mul_one]
      simp only [R,A,T,Matrix.mul_assoc]
    rw [ht,show (-R-1)*m.state.xi= -((R+1)*m.state.xi) by
      simp only [Matrix.neg_mul,Matrix.add_mul,Matrix.sub_mul]; abel,
      hs_eq_hsNorm,CountProof.hs_neg] at hc'
    exact hc'
  have hTc : hs (comm T m.state.xi)≤e := m.state_commutators 39 (by decide) (by decide)
  have hconj := conjugation A.conjTranspose T m.state.xi (ReturnProof.unitary_adjoint A hA) hT
  rw [inverse_defect _ _ hA] at hconj
  have hsplit : (R-1)*m.state.xi=
      A*((T*A.conjTranspose*T.conjTranspose-1)*m.state.xi)+(A-1)*m.state.xi := by
    simp only [R,Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc]
    abel
  have hsum := hsNorm_add_le (A*((T*A.conjTranspose*T.conjTranspose-1)*m.state.xi)) ((A-1)*m.state.xi)
  rw [hsNorm_unitary_left _ _ hA.1,←hsplit,←hs_eq_hsNorm,←hs_eq_hsNorm,←hs_eq_hsNorm] at hsum
  have hnorm := CountProof.hs_sub_le ((R+1)*m.state.xi) ((R-1)*m.state.xi)
  have htwo : (R+1)*m.state.xi-(R-1)*m.state.xi=(2:ℂ) • m.state.xi := by
    simp only [Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul]
    module
  rw [htwo,CountProof.hs_smul,show ‖(2:ℂ)‖=2 by norm_num,
    show hsNorm m.state.xi=1 from ReturnProof.state_xi_normalized m.state,mul_one,
    ←hs_eq_hsNorm,←hs_eq_hsNorm] at hnorm
  have hUa : U (inputPresentation.distinguished+1)=A := by
    change wordEval m.U (images 20)=m.U 20
    simp [images,wordEval]
  rw [hUa]
  change 1-14826*e≤hs ((A-1)*m.state.xi)
  nlinarith

theorem source_pullback {d : Nat} (U : Nat → Mat d) (s : State d) (e : ℝ)
    (he : 0≤e) (hm : presentationModel U s e) :
    ∃ V : Nat → Mat d, sourceModel V s (36780*e) ∧
      hs ((U (inputPresentation.distinguished+1)-1)*s.xi)-36780*e≤hs ((wordEval V lampJ-1)*s.xi) := by
  let V : Nat → Mat d := fun j => wordEval U (thetaImages j)
  have hV : ∀ j, IsUnitary (V j) := fun j => wordEval_unitary U hm.1 _
  have hdata : ∀ j : Fin 6, (thetaImages (j.val+1)).length≤3 ∧
      (thetaImages (j.val+1)).all (fun a => decide (1≤a.1 ∧ a.1≤27))=true := by decide +kernel
  have hcV : ∀ j, 1≤j → j≤6 → hs (comm (V j) s.xi)≤36780*e := by
    intro j hj1 hj6
    have hd := hdata ⟨j-1,by omega⟩
    simp only [Nat.sub_add_cancel hj1] at hd
    have hc := word_commutator_on U hm.1 s.xi e (thetaImages j) (by
      intro a ha
      have hb := of_decide_eq_true (List.all_eq_true.mp hd.2 a ha)
      exact hm.2.2 a.1 hb.1 hb.2)
    exact hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hd.1.trans (by decide : 3≤36780)) he)
  have hmodel : sourceModel V s (36780*e) := by
    refine ⟨hV,?_,hcV⟩
    intro w hw
    rw [show wordEval V w=wordEval U (thetaWord w) from
      (word_eval_substitution U hm.1 thetaImages w).trans (by rw [theta_substitution])]
    exact pauli_word_bound U s e he hm w hw
  refine ⟨V,hmodel,?_⟩
  let A := wordEval V lampJ
  let B := U 20
  let r : Word := lampJ.map (fun a => (a.1-1,a.2))++[(20,false)]
  let R := wordEval U r
  have hA : IsUnitary A := wordEval_unitary V hV _
  have hB : IsUnitary B := hm.1 _
  have hR : IsUnitary R := wordEval_unitary U hm.1 _
  have hR_eq : R=A*B.conjTranspose := by
    simp [R,r,A,B,V,wordEval,lampJ,thetaImages,thetaLetter,Matrix.mul_assoc]
  have hdef : hs ((R-1)*s.xi)≤5*e := by
    have hh := checked_weighted_bound (presentationRelator inputPresentation) U hm.1 s.xi e r
      visibilityCertificate 3 visibility_certificate_checked hm.2.1 (by
        intro f hf a ha
        have hsupp : visibilityCertificate.all (fun f => f.conjugator.all
            (fun a => decide (1≤a.1 ∧ a.1≤27)))=true := by decide +kernel
        have hb := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hsupp f hf) a ha)
        exact hm.2.2 a.1 hb.1 hb.2)
    exact hh
  have hcB : hs (comm B s.xi)≤e := hm.2.2 20 (by decide) (by decide)
  have hmove := ReturnProof.unitary_difference_right_transport R 1 B s.xi hR
    (by simp [IsUnitary]) hB
  have heq : (R-1)*B*s.xi=(A-B)*s.xi := by
    rw [hR_eq]
    simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,hB.1,Matrix.mul_one]
  rw [heq,←hs_eq_hsNorm,←hs_eq_hsNorm,←hs_eq_hsNorm] at hmove
  have hdiff : hs ((B-A)*s.xi)≤7*e := by
    rw [Matrix.sub_mul,hs_eq_hsNorm,CountProof.hs_sub_rev,←Matrix.sub_mul,←hs_eq_hsNorm]
    linarith
  have hsum := hsNorm_add_le ((B-A)*s.xi) ((A-1)*s.xi)
  have hsum_eq : (B-A)*s.xi+(A-1)*s.xi=(B-1)*s.xi := by
    simp only [Matrix.sub_mul]
    abel
  rw [hsum_eq,←hs_eq_hsNorm,←hs_eq_hsNorm,←hs_eq_hsNorm] at hsum
  change hs ((B-1)*s.xi)-36780*e≤hs ((A-1)*s.xi)
  linarith

theorem strategy_pullback (a b : Nat) (s : Strategy MainProof.concreteLCS a b) (eps : ℝ)
    (he : 0<eps) (hsmall : eps≤mainEps) (hw : 1-eps≤win s) :
    ∃ (d : Nat) (rho : State d) (U : Nat → Mat d), sourceModel U rho (cStar*Real.sqrt eps) ∧
      1/2≤hs ((wordEval U lampJ-1)*rho.xi) ∧
      entropy rho.rho=entropy (s.psi*s.psi.conjTranspose) := by
  let err := transferPrecision MainProof.concreteLCS eps
  obtain ⟨d,m,_,_,_,_,hJ,_,_,W,hW,hrec⟩ :=
    TransferProof.transfer MainProof.concreteLCS a b s eps he.le hw
  have herr : 0≤err := TransferProof.transferPrecision_nonneg _ _
  obtain ⟨U,hm,hv⟩ := model_pullback err herr m hJ
  obtain ⟨V,hV,hvis⟩ := source_pullback U m.state (cPsi*err)
    (mul_nonneg (by norm_num [cPsi]) herr) hm
  have hscale : 36780*(cPsi*err)=cStar*Real.sqrt eps := by
    dsimp [err]
    rw [ProfileProof.precision_eq,MainProof.concreteLCS_gameConstant]
    unfold cStar
    ring
  rw [hscale] at hV
  refine ⟨d,m.state,V,hV,?_,?_⟩
  · have he100 : eps≤(2:ℝ)^(-100:ℤ) := hsmall.trans
      (zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) (by norm_num : (-5500:ℤ)≤-100))
    have he30 : eps≤(1/10^30:ℝ) := he100.trans (by norm_num)
    have hsqrt : Real.sqrt eps≤(1/10^15:ℝ) := by
      nlinarith [Real.sq_sqrt he.le,Real.sqrt_nonneg eps]
    have h72 : Real.sqrt 5061≤72 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5061),Real.sqrt_nonneg (5061:ℝ)]
    have hcoeff : 36781*cPsi*(8*Real.sqrt 5061)≤(10:ℝ)^12 := by
      norm_num [cPsi]
      nlinarith
    have hloss : 36781*cPsi*err≤1/2 := by
      calc
        _=(36781*cPsi*(8*Real.sqrt 5061))*Real.sqrt eps := by
          dsimp [err]
          rw [ProfileProof.precision_eq,MainProof.concreteLCS_gameConstant]
          ring
        _≤(10:ℝ)^12*Real.sqrt eps := mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg eps)
        _≤(10:ℝ)^12*(1/10^15) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        _≤1/2 := by norm_num
    nlinarith
  · exact (ProfileProof.state_isometry_entropy m.state
      (State.ofQuAIR (CountProof.factorState s.psi s.normalized)) W hW hrec.symm).symm

end
end Blueprint.AWordArea

-- ROUND-12 DECLARATION AUDIT
#print axioms Blueprint.AWordArea.adjoint_commutator
#print axioms Blueprint.AWordArea.word_commutator
#print axioms Blueprint.AWordArea.conjugation
#print axioms Blueprint.AWordArea.inverse_defect
#print axioms Blueprint.AWordArea.product_defect
#print axioms Blueprint.AWordArea.factor_eval
#print axioms Blueprint.AWordArea.charged_area
#print axioms Blueprint.AWordArea.word_commutator_on
#print axioms Blueprint.AWordArea.word_eval_substitution
#print axioms Blueprint.AWordArea.factorCharge
#print axioms Blueprint.AWordArea.factor_charge_scale
#print axioms Blueprint.AWordArea.charged_area_local
#print axioms Blueprint.AWordArea.checked_weighted_bound
#print axioms Blueprint.AWordArea.pauliCertificate
#print axioms Blueprint.AWordArea.pauli_certificate_checked
#print axioms Blueprint.AWordArea.pauli_certificate_data
#print axioms Blueprint.AWordArea.thetaImages
#print axioms Blueprint.AWordArea.theta_substitution
#print axioms Blueprint.AWordArea.pauli_word_bound
#print axioms Blueprint.AWordArea.numericCertificate
#print axioms Blueprint.AWordArea.numeric_certificate_checked
#print axioms Blueprint.AWordArea.numeric_certificate_data
#print axioms Blueprint.AWordArea.numeric_word_bound
#print axioms Blueprint.AWordArea.visibilityCertificate
#print axioms Blueprint.AWordArea.visibility_certificate_checked
#print axioms Blueprint.AWordArea.short_conjugators
#print axioms Blueprint.AWordArea.model_pullback
#print axioms Blueprint.AWordArea.source_pullback
#print axioms Blueprint.AWordArea.strategy_pullback
