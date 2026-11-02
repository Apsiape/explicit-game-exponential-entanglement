import Blueprint.Definitions

namespace Blueprint.AGadget
noncomputable section
open Companion Companion.Analytic
open scoped BigOperators
set_option maxHeartbeats 600000

def concreteInput : GeneralGadget.Input where
  n0 := 26
  hasY := true
  distinguished := 19
  c0 := inputPresentation.c0.map (fun (a,b,c) => (Fin.ofNat 26 a,Fin.ofNat 26 b,Fin.ofNat 26 c))
  c1 := inputPresentation.c1.map (fun (b,c) => (Fin.ofNat 26 b,Fin.ofNat 26 c))
  c1_absent := by simp
  linear := inputPresentation.linear.map (List.map (Fin.ofNat 26))
  linear_nodup := by decide +kernel
  linear_small := by decide +kernel
  linear_order := by
    intro i
    fin_cases i <;> exact ⟨0,by decide +kernel⟩
  linear_commutations := by decide +kernel

def decodeHost (j : Nat) : GeneralGadget.Host concreteInput :=
  if j<26 then .inl (Fin.ofNat 26 j) else
  if j=26 then .inr (.inl ⟨0,by decide⟩) else
  if j=27 then .inr (.inr (.inl ⟨0,by decide⟩)) else
  if j<38 then .inr (.inr (.inr (.inl (Fin.ofNat 10 (j-28))))) else
  .inr (.inr (.inr (.inr (j≠38))))

def decodeTriple (j : Nat) : GeneralGadget.HostTriple concreteInput :=
  if j<76 then .inl (Fin.ofNat 76 j) else if j<96 then
    .inr (.inl (Fin.ofNat 10 ((j-76)/2),(j-76)%2=1)) else .inr (.inr ())

def decodeNice (j : Nat) : GeneralGadget.Nice concreteInput :=
  if j<40 then .inl (0,decodeHost j) else if j<80 then .inl (1,decodeHost (j-40)) else
  if j<120 then .inl (2,decodeHost (j-80)) else if j=120 then .inr (.inl ()) else
  if j<161 then .inl (3,decodeHost (j-121)) else
    .inr (.inr (decodeTriple ((j-161)/2),(j-161)%2=1))

def decodeNiceTriple (j : Nat) : GeneralGadget.NiceTriple concreteInput :=
  if j<40 then .inl (decodeHost j) else
    .inr (decodeTriple ((j-40)/2),(j-40)%2=1)

def decodeVariable (j : Nat) : GeneralGadget.Variable concreteInput :=
  if j<355 then .inl (decodeNice j) else
    .inr (decodeNiceTriple ((j-355)/7),Fin.ofNat 7 ((j-355)%7))

def equationNumber : GeneralGadget.EquationIndex concreteInput → Nat
  | .inl (.inl i) => i.val
  | .inl (.inr (.inl _)) => 8
  | .inl (.inr (.inr (.inl (a,b)))) => 9+2*GeneralGadget.hostNumber concreteInput a+b.toNat
  | .inl (.inr (.inr (.inr (t,b)))) => 89+2*GeneralGadget.tripleNumber concreteInput t+b.toNat
  | .inr (t,k) => 283+6*GeneralGadget.niceTripleNumber concreteInput t+k.val

def decodeEquation (j : Nat) : GeneralGadget.EquationIndex concreteInput :=
  if j<8 then .inl (.inl (Fin.ofNat 8 j)) else if j=8 then .inl (.inr (.inl ())) else
  if j<89 then .inl (.inr (.inr (.inl (decodeHost ((j-9)/2),(j-9)%2=1)))) else
  if j<283 then .inl (.inr (.inr (.inr (decodeTriple ((j-89)/2),(j-89)%2=1)))) else
    .inr (decodeNiceTriple ((j-283)/6),Fin.ofNat 6 ((j-283)%6))

theorem variable_number_bound : ∀ a : GeneralGadget.Variable concreteInput,
    GeneralGadget.variableNumber concreteInput a<suppliedGame.n := by decide +kernel

theorem equation_number_bound : ∀ a : GeneralGadget.EquationIndex concreteInput,
    equationNumber a<suppliedGame.equations.length := by decide +kernel

theorem variable_number_decode : ∀ j : Fin suppliedGame.n,
    GeneralGadget.variableNumber concreteInput (decodeVariable j.val)=j.val := by decide +kernel

theorem equation_number_decode : ∀ j : Fin suppliedGame.equations.length,
    equationNumber (decodeEquation j.val)=j.val := by decide +kernel

def numericVariable : GeneralGadget.Variable concreteInput → Fin suppliedGame.n :=
  fun a => ⟨GeneralGadget.variableNumber concreteInput a,variable_number_bound a⟩

def numericEquation : GeneralGadget.EquationIndex concreteInput → Fin suppliedGame.equations.length :=
  fun a => ⟨equationNumber a,equation_number_bound a⟩

def variableEquiv : GeneralGadget.Variable concreteInput ≃ Fin suppliedGame.n :=
  Equiv.ofBijective numericVariable ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨
    fun j => ⟨decodeVariable j.val,Fin.ext (variable_number_decode j)⟩,by decide +kernel⟩)

def equationEquiv : GeneralGadget.EquationIndex concreteInput ≃ Fin suppliedGame.equations.length :=
  Equiv.ofBijective numericEquation ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨
    fun j => ⟨decodeEquation j.val,Fin.ext (equation_number_decode j)⟩,by decide +kernel⟩)

theorem decoded_rows_match : (List.ofFn (fun j : Fin suppliedGame.equations.length =>
    let r := GeneralGadget.systemEquation concreteInput (decodeEquation j.val)
    (⟨r.vars.map (GeneralGadget.variableNumber concreteInput),r.rhs⟩:Companion.Equation)))=suppliedGame.equations := by
  decide +kernel

theorem raw_rows_match (i : GeneralGadget.EquationIndex concreteInput) :
    ((GeneralGadget.systemEquation concreteInput i).vars.map (GeneralGadget.variableNumber concreteInput)).Perm
      suppliedGame.equations[(numericEquation i).val].vars ∧
    (GeneralGadget.systemEquation concreteInput i).rhs=suppliedGame.equations[(numericEquation i).val].rhs := by
  have hi : decodeEquation (numericEquation i).val=i := by
    apply equationEquiv.injective
    exact Fin.ext (equation_number_decode (numericEquation i))
  have hh := congrArg (fun rs : List Companion.Equation => rs[(numericEquation i).val]?) decoded_rows_match
  simp only [List.getElem?_ofFn,(numericEquation i).isLt,↓reduceDIte,hi] at hh
  rw [List.getElem?_eq_getElem (numericEquation i).isLt] at hh
  have heq := Option.some.inj hh
  exact ⟨heq ▸ List.Perm.refl _,congrArg Companion.Equation.rhs heq⟩

def typedPresentationMatches (p : GeneralGadget.Input) : Prop :=
  p.n0=inputPresentation.n0 ∧ p.hasY=true ∧ p.distinguished.val=inputPresentation.distinguished ∧
  p.c0.map (fun (a,b,c) => (a.val,b.val,c.val))=inputPresentation.c0 ∧
  p.c1.map (fun (a,b) => (a.val,b.val))=inputPresentation.c1 ∧
  p.linear.map (List.map Fin.val)=inputPresentation.linear

def numericIdentification (p : GeneralGadget.Input)
    (v : GeneralGadget.Variable p ≃ Fin suppliedGame.n)
    (q : GeneralGadget.EquationIndex p ≃ Fin suppliedGame.equations.length) : Prop :=
  ∀ i, ((GeneralGadget.orderedEquation p i).vars.map (fun a => (v a).val)=
      (suppliedGame.equations[(q i).val]).vars) ∧
    (GeneralGadget.orderedEquation p i).rhs=(suppliedGame.equations[(q i).val]).rhs

/-- RESULT-6 step 1: actual typed/numeric row identification. -/
theorem identify : ∃ p : GeneralGadget.Input, typedPresentationMatches p ∧
    ∃ v q, numericIdentification p v q := by
  refine ⟨concreteInput,by unfold typedPresentationMatches; decide +kernel,variableEquiv,equationEquiv,?_⟩
  intro i
  obtain ⟨hperm,hrhs⟩ := raw_rows_match i
  refine ⟨?_,hrhs⟩
  have hs : ((GeneralGadget.orderedEquation concreteInput i).vars.map
      (GeneralGadget.variableNumber concreteInput)).Pairwise (· < ·) := by
    have hh := Classical.choose_spec (GeneralGadget.rows_cyclic_numbered concreteInput i)
    simpa only [GeneralGadget.orderedEquation,GeneralGadget.rowRotation,List.pairwise_map] using hh
  have hp := ((List.rotate_perm (GeneralGadget.systemEquation concreteInput i).vars
    (GeneralGadget.rowRotation concreteInput i)).map (GeneralGadget.variableNumber concreteInput)).trans hperm
  have ht := MainProof.supplied_rows_sorted _
    (List.getElem_mem (numericEquation i).isLt)
  exact hp.eq_of_pairwise' hs ht

def sourceNumber : GeneralGadget.Source concreteInput → Nat
  | .inl a => a.val+1
  | .inr _ => 27

def sourceRename : FreeGroup (GeneralGadget.Source concreteInput) →* FreeGroup Nat :=
  FreeGroup.lift (fun a => FreeGroup.of (sourceNumber a))

def sourceWord : GeneralGadget.SourceRel concreteInput → Word
  | .inl a => [pos a.val,pos a.val]
  | .inr (.inl i) => (concreteInput.linear[i]).map (fun a => pos a.val)
  | .inr (.inr (.inl i)) =>
    let (a,b,c) := concreteInput.c0[i]
    [pos a.val,pos b.val,pos a.val,neg c.val]
  | .inr (.inr (.inr i)) =>
    let (b,c) := concreteInput.c1[i]
    [pos 26,pos b.val,neg 26,neg c.val]

theorem source_word_matches : ∀ i : GeneralGadget.SourceRel concreteInput,
    sourceRename (GeneralGadget.sourceRelator concreteInput i)=FreeGroup.mk (sourceWord i) := by
  decide +kernel

theorem source_word_mem : ∀ i : GeneralGadget.SourceRel concreteInput,
    sourceWord i∈presentationWords inputPresentation := by decide +kernel

def sourcePhi {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j)) :
    FreeGroup (GeneralGadget.Source concreteInput) →* DoubleMatrix.U (Fin d) :=
  (assignmentHom U hU).comp sourceRename

theorem source_phi_bounds {d : Nat} (U : Nat → Mat d) (e : ℝ)
    (hR : normalizedRepresentation (presentationWords inputPresentation) U e) :
    ∀ i, DoubleMatrix.defect (sourcePhi U hR.1 (GeneralGadget.sourceRelator concreteInput i))≤e := by
  intro i
  have hh := hR.2 (sourceWord i) (source_word_mem i)
  simpa only [sourcePhi,MonoidHom.comp_apply,source_word_matches,assignmentHom_word,
    DoubleMatrix.defect,DoubleMatrix.sizeNorm,normalizedHS,Fintype.card_fin,div_eq_mul_inv,mul_comm] using hh

theorem source_phi_distinguished {d : Nat} (U : Nat → Mat d) (hU : ∀ j, IsUnitary (U j))
    (hw : U (inputPresentation.distinguished+1)=-1) :
    sourcePhi U hU (GeneralGadget.srcOld concreteInput.distinguished)=ScalarPhase.minusOne (Fin d) := by
  apply Subtype.ext
  simp only [sourcePhi,MonoidHom.comp_apply,GeneralGadget.srcOld,sourceRename,
    FreeGroup.lift_apply_of,sourceNumber,assignmentHom,asUnitary,ScalarPhase.minusOne]
  exact hw

def reindexUnitary {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) : DoubleMatrix.U a →* DoubleMatrix.U b where
  toFun U := ⟨Matrix.reindexAlgEquiv ℂ ℂ e (U:Matrix a a ℂ),by
    let T := Matrix.reindexAlgEquiv ℂ ℂ e
    have hs (M : Matrix a a ℂ) : (T M).conjTranspose=T M.conjTranspose := rfl
    have h1 : (U:Matrix a a ℂ).conjTranspose*(U:Matrix a a ℂ)=1 := U.property.1
    have h2 : (U:Matrix a a ℂ)*(U:Matrix a a ℂ).conjTranspose=1 := U.property.2
    constructor
    · change (T (U:Matrix a a ℂ)).conjTranspose*T (U:Matrix a a ℂ)=1
      rw [hs,←map_mul,h1,map_one]
    · change T (U:Matrix a a ℂ)*(T (U:Matrix a a ℂ)).conjTranspose=1
      rw [hs,←map_mul,h2,map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' U V := Subtype.ext (map_mul _ _ _)

theorem reindex_hs {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (M : Matrix a a ℂ) : hsNorm (Matrix.reindexAlgEquiv ℂ ℂ e M)=hsNorm M := by
  unfold hsNorm hsSquared
  apply congrArg Real.sqrt
  change (∑ i : b, ∑ j : b, Complex.normSq (M (e.symm i) (e.symm j)))=
    ∑ i : a, ∑ j : a, Complex.normSq (M i j)
  calc
    _=∑ i : b, ∑ j : a, Complex.normSq (M (e.symm i) j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.symm.sum_comp (fun j => Complex.normSq (M (e.symm i) j))
    _=_ := e.symm.sum_comp (fun i => ∑ j : a, Complex.normSq (M i j))

theorem reindex_defect {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (U : DoubleMatrix.U a) :
    DoubleMatrix.defect (reindexUnitary e U)=DoubleMatrix.defect U := by
  change hsNorm (Matrix.reindexAlgEquiv ℂ ℂ e (U:Matrix a a ℂ)-1)/Real.sqrt (Fintype.card b)=_
  rw [←map_one (Matrix.reindexAlgEquiv ℂ ℂ e),←map_sub,reindex_hs,←Fintype.card_congr e]
  rfl

theorem decode_variable_number (a : GeneralGadget.Variable concreteInput) :
    decodeVariable (GeneralGadget.variableNumber concreteInput a)=a := by
  apply variableEquiv.injective
  exact Fin.ext (variable_number_decode (numericVariable a))

def typedLetter (j : Nat) : FreeGroup (Option (GeneralGadget.Variable concreteInput)) :=
  if j=suppliedGame.n+1 then FreeGroup.of none else
    if 1≤j ∧ j≤suppliedGame.n then FreeGroup.of (some (decodeVariable (j-1))) else 1

def typedLift : FreeGroup Nat →* FreeGroup (Option (GeneralGadget.Variable concreteInput)) :=
  FreeGroup.lift typedLetter

theorem typed_letter_variable (j : Nat) (hj : j<suppliedGame.n) :
    typedLetter (j+1)=FreeGroup.of (some (decodeVariable j)) := by
  have hne : j+1≠suppliedGame.n+1 := by omega
  unfold typedLetter
  rw [if_neg hne,if_pos (show 1≤j+1 ∧ j+1≤suppliedGame.n by omega)]
  simp only [Nat.add_sub_cancel]

theorem typed_letter_J : typedLetter (suppliedGame.n+1)=FreeGroup.of none := by simp [typedLetter]

theorem typed_lift_positive (vs : List Nat) (hb : ∀ j∈vs, j<suppliedGame.n) :
    typedLift (FreeGroup.mk (vs.map pos))=
      (vs.map (fun j => FreeGroup.of (some (decodeVariable j)))).prod := by
  simp only [typedLift,FreeGroup.lift_mk,List.map_map,Function.comp_def,pos,↓reduceIte]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  exact typed_letter_variable j (hb j hj)

theorem concrete_rows : numericIdentification concreteInput variableEquiv equationEquiv := by
  intro i
  obtain ⟨hperm,hrhs⟩ := raw_rows_match i
  refine ⟨?_,hrhs⟩
  have hs : ((GeneralGadget.orderedEquation concreteInput i).vars.map
      (GeneralGadget.variableNumber concreteInput)).Pairwise (· < ·) := by
    have hh := Classical.choose_spec (GeneralGadget.rows_cyclic_numbered concreteInput i)
    simpa only [GeneralGadget.orderedEquation,GeneralGadget.rowRotation,List.pairwise_map] using hh
  have hp := ((List.rotate_perm (GeneralGadget.systemEquation concreteInput i).vars
    (GeneralGadget.rowRotation concreteInput i)).map (GeneralGadget.variableNumber concreteInput)).trans hperm
  have ht := MainProof.supplied_rows_sorted _ (List.getElem_mem (numericEquation i).isLt)
  exact hp.eq_of_pairwise' hs ht

theorem ordered_numeric_rows (i : Fin suppliedGame.equations.length) :
    ((GeneralGadget.orderedEquation concreteInput (equationEquiv.symm i)).vars.map
      (GeneralGadget.variableNumber concreteInput))=suppliedGame.equations[i.val].vars ∧
    (GeneralGadget.orderedEquation concreteInput (equationEquiv.symm i)).rhs=suppliedGame.equations[i.val].rhs := by
  have hh := concrete_rows (equationEquiv.symm i)
  simp only [Equiv.apply_symm_apply] at hh
  convert hh using 1 <;> rfl

theorem decode_numeric_row (i : Fin suppliedGame.equations.length) :
    (suppliedGame.equations[i.val].vars.map decodeVariable)=
      (GeneralGadget.orderedEquation concreteInput (equationEquiv.symm i)).vars := by
  rw [←(ordered_numeric_rows i).1,List.map_map]
  simp [Function.comp_def,decode_variable_number]

theorem typed_lift_row (i : Fin suppliedGame.equations.length) :
    typedLift (FreeGroup.mk ((if suppliedGame.equations[i.val].rhs then [pos suppliedGame.n] else [])++
      suppliedGame.equations[i.val].vars.map pos))=
        GeneralGadget.orderedRelator concreteInput (.inr (.inr (.inl (equationEquiv.symm i)))) := by
  classical
  rw [←FreeGroup.mul_mk,map_mul,typed_lift_positive _ (by
    intro j hj
    exact (MainProof.supplied_row_data _ (List.getElem_mem i.isLt)).2.2 j hj)]
  have hm : (suppliedGame.equations[i.val].vars.map (fun j => FreeGroup.of (some (decodeVariable j))))=
      ((GeneralGadget.orderedEquation concreteInput (equationEquiv.symm i)).vars.map
        (fun a => FreeGroup.of (some a))) := by
    rw [←decode_numeric_row,List.map_map]
    rfl
  rw [hm]
  dsimp only [GeneralGadget.orderedRelator]
  rw [(ordered_numeric_rows i).2]
  cases hh : suppliedGame.equations[i.val].rhs <;>
    simp [typedLift,FreeGroup.lift_mk,pos,typed_letter_J,←FreeGroup.one_eq_mk]

theorem numeric_relator_typed (key : RelKey) (r : Word) (hr : relator suppliedGame key=some r) :
    ∃ i : GeneralGadget.RelationIndex concreteInput,
      typedLift (FreeGroup.mk r)=GeneralGadget.orderedRelator concreteInput i := by
  classical
  cases key with
  | square j =>
    simp only [relator] at hr
    split at hr
    next hj =>
      cases Option.some.inj hr
      refine ⟨.inl (some (decodeVariable j)),?_⟩
      simp [typedLift,FreeGroup.lift_mk,pos,typed_letter_variable j hj,GeneralGadget.orderedRelator]
    next => cases hr
  | centralSquare =>
    cases Option.some.inj hr
    refine ⟨.inl none,?_⟩
    simp [typedLift,FreeGroup.lift_mk,pos,typed_letter_J,GeneralGadget.orderedRelator]
  | central j =>
    simp only [relator] at hr
    split at hr
    next hj =>
      cases Option.some.inj hr
      refine ⟨.inr (.inl (decodeVariable j)),?_⟩
      simp [typedLift,FreeGroup.lift_mk,pos,neg,typed_letter_variable j hj,typed_letter_J,
        GeneralGadget.orderedRelator,mul_assoc]
    next => cases hr
  | equation row =>
    simp only [relator] at hr
    cases hg : suppliedGame.equations[row]? with
    | none => simp [hg] at hr
    | some eqn =>
      simp only [hg,Option.bind_some] at hr
      change (if eqn.vars.all (· < suppliedGame.n) then
        some ((if eqn.rhs then [pos suppliedGame.n] else [])++eqn.vars.map pos) else none)=some r at hr
      split at hr
      next =>
        cases Option.some.inj hr
        obtain ⟨hidx,heq⟩ := List.getElem?_eq_some_iff.mp hg
        subst eqn
        exact ⟨.inr (.inr (.inl (equationEquiv.symm ⟨row,hidx⟩))),typed_lift_row ⟨row,hidx⟩⟩
      next => cases hr
  | commute row j k =>
    simp only [relator] at hr
    cases hg : suppliedGame.equations[row]? with
    | none => simp [hg] at hr
    | some eqn =>
      simp only [hg,Option.bind_some] at hr
      change (if j<suppliedGame.n ∧ k<suppliedGame.n ∧ j∈eqn.vars ∧ k∈eqn.vars then
        some [pos j,pos k,neg j,neg k] else none)=some r at hr
      split at hr
      next hc =>
        cases Option.some.inj hr
        obtain ⟨hidx,heq⟩ := List.getElem?_eq_some_iff.mp hg
        subst eqn
        let q := equationEquiv.symm (⟨row,hidx⟩:Fin suppliedGame.equations.length)
        have hm (j : Nat) (hj : j∈suppliedGame.equations[row].vars) :
            decodeVariable j∈(GeneralGadget.orderedEquation concreteInput q).vars := by
          have hh : decodeVariable j∈suppliedGame.equations[row].vars.map decodeVariable :=
            List.mem_map.mpr ⟨j,hj,rfl⟩
          rwa [decode_numeric_row ⟨row,hidx⟩] at hh
        refine ⟨.inr (.inr (.inr (q,decodeVariable j,decodeVariable k))),?_⟩
        simp [typedLift,FreeGroup.lift_mk,pos,neg,typed_letter_variable j hc.1,
          typed_letter_variable k hc.2.1,GeneralGadget.orderedRelator,
          hm j hc.2.2.1,hm k hc.2.2.2,mul_assoc]
      next => cases hr
  | conjugacy _ => cases hr
  | pConjugacy _ => cases hr

/-- Transport G3 through identify, including the source substitution. -/
theorem extend (d : Nat) (hd : 0<d) (U : Nat → Mat d) (e : ℝ) (he : 0≤e)
    (hR : normalizedRepresentation (presentationWords inputPresentation) U e)
    (hw : U (inputPresentation.distinguished+1)=-1) :
    ∃ V : Nat → Mat (8*d), (∀ j, IsUnitary (V j)) ∧
      (∀ k r, relator suppliedGame k=some r → normalizedHS (wordEval V r-1)≤3*e) ∧
      V (suppliedGame.n+1)=-1 := by
  let phi := sourcePhi U hR.1
  obtain ⟨hb,hJ,hcard⟩ := GeneralGadget.ordered_G3 concreteInput d hd phi e he
    (source_phi_bounds U e hR) (source_phi_distinguished U hR.1 hw)
  let E : GeneralGadget.Amplified (Fin d) ≃ Fin (8*d) := Fintype.equivFinOfCardEq hcard
  let H : FreeGroup Nat →* DoubleMatrix.U (Fin (8*d)) :=
    (reindexUnitary E).comp ((GeneralGadget.globalHom concreteInput phi).comp typedLift)
  let V : Nat → Mat (8*d) := fun j => H (FreeGroup.of j)
  have hV : ∀ j, IsUnitary (V j) := fun j => (H (FreeGroup.of j)).property
  have hword (w : Word) : wordEval V w=(H (FreeGroup.mk w):Mat (8*d)) := by
    rw [←assignmentHom_word V hV]
    have hh : assignmentHom V hV=H := by
      apply FreeGroup.ext_hom
      intro j
      apply Subtype.ext
      simp only [assignmentHom,FreeGroup.lift_apply_of,asUnitary]
      rfl
    rw [hh]
  refine ⟨V,hV,?_,?_⟩
  · intro key r hr
    obtain ⟨i,hi⟩ := numeric_relator_typed key r hr
    rw [hword]
    have hn : normalizedHS ((H (FreeGroup.mk r):Mat (8*d))-1)=DoubleMatrix.defect (H (FreeGroup.mk r)) := by
      simp only [normalizedHS,DoubleMatrix.defect,DoubleMatrix.sizeNorm,Fintype.card_fin,div_eq_mul_inv,mul_comm]
    rw [hn]
    change DoubleMatrix.defect (reindexUnitary E
      (GeneralGadget.globalHom concreteInput phi (typedLift (FreeGroup.mk r))))≤3*e
    rw [reindex_defect,hi]
    exact hb i
  · change ((reindexUnitary E)
      (GeneralGadget.globalHom concreteInput phi (typedLift (FreeGroup.of (suppliedGame.n+1)))):
        Mat (8*d))=-1
    simp only [typedLift,FreeGroup.lift_apply_of,typed_letter_J]
    change Matrix.reindexAlgEquiv ℂ ℂ E
      (GeneralGadget.globalHom concreteInput phi (FreeGroup.of none):
        Matrix (GeneralGadget.Amplified (Fin d)) (GeneralGadget.Amplified (Fin d)) ℂ)=-1
    rw [hJ,map_neg,map_one]


end
end Blueprint.AGadget

-- ROUND-12 DECLARATION AUDIT
#print axioms Blueprint.AGadget.concreteInput
#print axioms Blueprint.AGadget.decodeHost
#print axioms Blueprint.AGadget.decodeTriple
#print axioms Blueprint.AGadget.decodeNice
#print axioms Blueprint.AGadget.decodeNiceTriple
#print axioms Blueprint.AGadget.decodeVariable
#print axioms Blueprint.AGadget.equationNumber
#print axioms Blueprint.AGadget.decodeEquation
#print axioms Blueprint.AGadget.variable_number_bound
#print axioms Blueprint.AGadget.equation_number_bound
#print axioms Blueprint.AGadget.variable_number_decode
#print axioms Blueprint.AGadget.equation_number_decode
#print axioms Blueprint.AGadget.numericVariable
#print axioms Blueprint.AGadget.numericEquation
#print axioms Blueprint.AGadget.variableEquiv
#print axioms Blueprint.AGadget.equationEquiv
#print axioms Blueprint.AGadget.decoded_rows_match
#print axioms Blueprint.AGadget.raw_rows_match
#print axioms Blueprint.AGadget.typedPresentationMatches
#print axioms Blueprint.AGadget.numericIdentification
#print axioms Blueprint.AGadget.identify
#print axioms Blueprint.AGadget.sourceNumber
#print axioms Blueprint.AGadget.sourceRename
#print axioms Blueprint.AGadget.sourceWord
#print axioms Blueprint.AGadget.source_word_matches
#print axioms Blueprint.AGadget.source_word_mem
#print axioms Blueprint.AGadget.sourcePhi
#print axioms Blueprint.AGadget.source_phi_bounds
#print axioms Blueprint.AGadget.source_phi_distinguished
#print axioms Blueprint.AGadget.reindexUnitary
#print axioms Blueprint.AGadget.reindex_hs
#print axioms Blueprint.AGadget.reindex_defect
#print axioms Blueprint.AGadget.decode_variable_number
#print axioms Blueprint.AGadget.typedLetter
#print axioms Blueprint.AGadget.typedLift
#print axioms Blueprint.AGadget.typed_letter_variable
#print axioms Blueprint.AGadget.typed_letter_J
#print axioms Blueprint.AGadget.typed_lift_positive
#print axioms Blueprint.AGadget.concrete_rows
#print axioms Blueprint.AGadget.ordered_numeric_rows
#print axioms Blueprint.AGadget.decode_numeric_row
#print axioms Blueprint.AGadget.typed_lift_row
#print axioms Blueprint.AGadget.numeric_relator_typed
#print axioms Blueprint.AGadget.extend
