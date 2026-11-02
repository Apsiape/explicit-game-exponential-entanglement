import Blueprint.Definitions
import Companion.AreaEstimate

namespace Blueprint.Published
open Companion

abbrev WordFactor := Word × Word × Bool

def wordFactorValue (f : WordFactor) : FreeGroup Nat :=
  FreeGroup.mk f.1*(if f.2.2 then FreeGroup.mk f.2.1 else (FreeGroup.mk f.2.1)⁻¹)*
    (FreeGroup.mk f.1)⁻¹

def finiteWordArea (R : Finset Word) (w : Word) (k : Nat) : Prop :=
  ∃ fs : List WordFactor, fs.length≤k ∧ (∀ f∈fs, f.2.1∈R) ∧
    (fs.map wordFactorValue).prod=FreeGroup.mk w

/-- Exact named literature input: Mghirbi--Douglas, v1.0.0, Lemma 3.4
(Conjugator lengths). R is a finite set of relator words; no restriction
on the number of generators is imposed in that lemma. Area is expanded
as its defining product of conjugates. No term is supplied here. -/
def ConjugatorLengths : Prop := ∀ (R : Finset Word) (K k : Nat) (w : Word),
  (∀ r∈R, r.length≤K) → finiteWordArea R w k →
  ∃ fs : List WordFactor, fs.length≤k ∧ (∀ f∈fs, f.2.1∈R) ∧
    (fs.map wordFactorValue).prod=FreeGroup.mk w ∧
    ∀ f∈fs, f.1.length≤w.length+k*K

end Blueprint.Published

namespace Blueprint.AWordAreaProof
noncomputable section
open Companion Published

theorem factor_to_word (rfn : RelKey → Option Word) (f : Factor) :
    wordFactorValue (f.conjugator,(rfn f.key).getD [],f.positive)=
      FreeGroup.mk (factorWordWith rfn f) := by
  cases hb : f.positive <;>
    simp only [wordFactorValue,factorWordWith,hb,Bool.false_eq_true,↓reduceIte,
      ←FreeGroup.mul_mk,←FreeGroup.inv_mk]

/-- The finite-set lemma applies even when the relator lookup has infinitely
many keys: extract the finitely many relators in the given filling, then
recover a valid original key for every relator in the shortened filling. -/
theorem short_conjugators_of_finite (hlit : ConjugatorLengths)
    (rfn : RelKey → Option Word) (K k : Nat) (w : Word)
    (hr : ∀ a r, rfn a=some r → r.length≤K) (ha : HasAreaWith rfn w k) :
    ∃ fs : List Factor, fs.length≤k ∧ (∀ f∈fs, (rfn f.key).isSome=true) ∧
      FreeGroup.mk (expandWith rfn fs)=FreeGroup.mk w ∧
      ∀ f∈fs, f.conjugator.length≤w.length+k*K := by
  classical
  letI : Nonempty RelKey := ⟨.centralSquare⟩
  obtain ⟨fs,hfs,hvalid,he⟩ := ha
  let R : Finset Word := (fs.map (fun f => (rfn f.key).getD [])).toFinset
  have hkey : ∀ r∈R, ∃ key, rfn key=some r := by
    intro r hr'
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr')
    cases hk : rfn f.key with
    | none => have hh := hvalid f hf; simp [hk] at hh
    | some r => exact ⟨f.key,hk⟩
  have hR : ∀ r∈R, r.length≤K := by
    intro r hr'
    obtain ⟨key,hk⟩ := hkey r hr'
    exact hr key r hk
  let F : Factor → WordFactor := fun f => (f.conjugator,(rfn f.key).getD [],f.positive)
  have harea : finiteWordArea R w k := by
    refine ⟨fs.map F,by simpa using hfs,?_,?_⟩
    · intro f hf
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨g,hg,rfl⟩)
    · simpa only [List.map_map,Function.comp_def,F,factor_to_word,←mk_expandWith] using he
  obtain ⟨gs,hgs,hmem,hprod,hshort⟩ := hlit R K k w hR harea
  let key : Word → RelKey := fun r => Classical.epsilon (fun key => rfn key=some r)
  have hk : ∀ r∈R, rfn (key r)=some r := fun r hr' => Classical.epsilon_spec (hkey r hr')
  let G : WordFactor → Factor := fun f => ⟨key f.2.1,f.2.2,f.1⟩
  refine ⟨gs.map G,by simpa using hgs,?_,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    simp only [G,hk g.2.1 (hmem g hg),Option.isSome_some]
  · rw [mk_expandWith,List.map_map]
    calc
      _=(gs.map wordFactorValue).prod := by
        congr 1
        apply List.map_congr_left
        intro g hg
        change FreeGroup.mk (factorWordWith rfn (G g))=wordFactorValue g
        rw [←factor_to_word]
        simp only [G,hk g.2.1 (hmem g hg),Option.getD_some]
      _=FreeGroup.mk w := hprod
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact hshort g hg

end
end Blueprint.AWordAreaProof

#print axioms Blueprint.Published.WordFactor
#print axioms Blueprint.Published.wordFactorValue
#print axioms Blueprint.Published.finiteWordArea
#print axioms Blueprint.Published.ConjugatorLengths
#print axioms Blueprint.AWordAreaProof.factor_to_word
#print axioms Blueprint.AWordAreaProof.short_conjugators_of_finite
