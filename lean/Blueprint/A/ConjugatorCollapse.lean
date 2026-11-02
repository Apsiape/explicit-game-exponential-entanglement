import Blueprint.A.ConjugatorLengths
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
Local, fully proved parts of the outer-face argument in state.tex, Lemma 3.4.
This module does NOT prove ConjugatorLengths. In particular it does not assert
that an arbitrary finiteWordArea witness admits the collapses defined below.
No definition from a different diagram formalization is used.
-/

namespace Blueprint.ConjugatorCollapse
open Companion Published
set_option maxHeartbeats 600000

def signedWord (r : Word) (b : Bool) : Word :=
  if b then r else FreeGroup.invRev r

theorem signedWord_length (r : Word) (b : Bool) :
    (signedWord r b).length = r.length := by
  cases b <;> simp [signedWord, FreeGroup.invRev_length]

theorem signedWord_mk (r : Word) (b : Bool) :
    FreeGroup.mk (signedWord r b) =
      if b then FreeGroup.mk r else (FreeGroup.mk r)⁻¹ := by
  cases b <;> simp [signedWord, FreeGroup.inv_mk]

def stem (r : Word) (b : Bool) : Word :=
  FreeGroup.reduceCyclically.conjugator (FreeGroup.reduce (signedWord r b))

def core (r : Word) (b : Bool) : Word :=
  FreeGroup.reduceCyclically (FreeGroup.reduce (signedWord r b))

theorem stem_core_decomposition (r : Word) (b : Bool) :
    stem r b ++ core r b ++ FreeGroup.invRev (stem r b) =
      FreeGroup.reduce (signedWord r b) :=
  FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically _

theorem core_cyclicallyReduced (r : Word) (b : Bool) :
    FreeGroup.IsCyclicallyReduced (core r b) := by
  apply FreeGroup.reduceCyclically.isCyclicallyReduced
  exact FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem

theorem stem_core_length (r : Word) (b : Bool) :
    2 * (stem r b).length + (core r b).length ≤ r.length := by
  have h := (FreeGroup.reduce.red (L := signedWord r b)).length_le
  rw [← stem_core_decomposition, List.length_append, List.length_append,
    FreeGroup.invRev_length, signedWord_length] at h
  omega

theorem original_factor_from_core (r : Word) (b : Bool) :
    wordFactorValue ([],r,b) =
      FreeGroup.mk (stem r b) * FreeGroup.mk (core r b) *
        (FreeGroup.mk (stem r b))⁻¹ := by
  have h := congrArg (FreeGroup.mk (α := Nat)) (stem_core_decomposition r b)
  rw [FreeGroup.reduce.self] at h
  simpa only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, signedWord_mk,
    wordFactorValue, ← FreeGroup.one_eq_mk, one_mul, inv_one, mul_one] using h.symm

/-- A rotated cyclic core is a conjugate of the ORIGINAL relator, with its
original orientation bit. The returned conjugator includes the cyclic stem. -/
theorem original_factor_from_rotation (r : Word) (b : Bool) (p q : Word)
    (hc : core r b = p ++ q) :
    wordFactorValue (FreeGroup.invRev p ++ FreeGroup.invRev (stem r b),r,b) =
      FreeGroup.mk (q ++ p) := by
  have h := original_factor_from_core r b
  simp only [wordFactorValue, ← FreeGroup.one_eq_mk, one_mul, inv_one, mul_one] at h
  simp only [wordFactorValue, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  rw [h, hc, ← FreeGroup.mul_mk]
  group

theorem rotation_conjugator_length (r : Word) (b : Bool) (p q : Word) (K : Nat)
    (hr : r.length ≤ K) (hc : core r b = p ++ q) (hq : q ≠ []) :
    (FreeGroup.invRev p ++ FreeGroup.invRev (stem r b)).length + 1 ≤ K := by
  have h := stem_core_length r b
  have hq' : 1 ≤ q.length := by
    have : q.length ≠ 0 := fun h => hq (List.length_eq_zero_iff.mp h)
    omega
  rw [hc, List.length_append] at h
  simp only [List.length_append, FreeGroup.invRev_length]
  omega

/-- One genuine combinatorial face collapse: replace a single outer edge by
the rest of its incident face. The face label must have an explicit short
conversion to an original relator; it is not silently treated as a new one. -/
structure FaceCollapse (R : Finset Word) (K : Nat) (u v : Word) where
  before : Word
  after : Word
  edge : Nat × Bool
  replacement : Word
  original : Word
  positive : Bool
  transport : Word
  original_mem : original ∈ R
  source : u = before ++ [edge] ++ after
  target : v = before ++ replacement ++ after
  perimeter : replacement.length + 1 ≤ K
  transport_length : transport.length + 1 ≤ K
  face_value : FreeGroup.mk ([edge] ++ FreeGroup.invRev replacement) =
    wordFactorValue (transport,original,positive)

/-- Mathlib's cyclic reduction is faithful for FaceCollapse, even when the
original relator is unreduced, not cyclically reduced, or negatively oriented. -/
theorem faceCollapse_of_rotation (R : Finset Word) (K : Nat)
    (r : Word) (b : Bool) (p q a d z : Word) (e : Nat × Bool)
    (hr : r ∈ R) (hK : r.length ≤ K) (hc : core r b = p ++ q)
    (hq : q ≠ []) (he : q ++ p = [e] ++ FreeGroup.invRev d) :
    Nonempty (FaceCollapse R K (a ++ [e] ++ z) (a ++ d ++ z)) := by
  have hl := stem_core_length r b
  have he' := congrArg List.length he
  simp only [List.length_append, List.length_singleton, FreeGroup.invRev_length] at he'
  rw [hc, List.length_append] at hl
  refine ⟨⟨a,z,e,d,r,b,FreeGroup.invRev p ++ FreeGroup.invRev (stem r b),
    hr,rfl,rfl,by omega,rotation_conjugator_length r b p q K hK hc hq,?_⟩⟩
  rw [original_factor_from_rotation r b p q hc, he]

namespace FaceCollapse

def factor {R : Finset Word} {K : Nat} {u v : Word}
    (c : FaceCollapse R K u v) : WordFactor :=
  (c.before ++ c.transport,c.original,c.positive)

theorem boundary_length {R : Finset Word} {K : Nat} {u v : Word}
    (c : FaceCollapse R K u v) : v.length ≤ u.length + K := by
  have hs := congrArg List.length c.source
  have ht := congrArg List.length c.target
  simp only [List.length_append, List.length_singleton] at hs ht
  have hp := c.perimeter
  omega

theorem factor_length {R : Finset Word} {K : Nat} {u v : Word}
    (c : FaceCollapse R K u v) : c.factor.1.length ≤ u.length + K := by
  have hs := congrArg List.length c.source
  simp only [List.length_append, List.length_singleton] at hs
  have ht := c.transport_length
  simp only [factor, List.length_append]
  omega

theorem factor_mem {R : Finset Word} {K : Nat} {u v : Word}
    (c : FaceCollapse R K u v) : c.factor.2.1 ∈ R := c.original_mem

theorem factor_value {R : Finset Word} {K : Nat} {u v : Word}
    (c : FaceCollapse R K u v) :
    FreeGroup.mk u = wordFactorValue c.factor * FreeGroup.mk v := by
  have he := c.face_value
  simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk] at he
  simp only [c.source,c.target]
  simp only [factor,wordFactorValue,← FreeGroup.mul_mk]
  simp only [wordFactorValue] at he
  calc
    _ = FreeGroup.mk c.before *
        (FreeGroup.mk [c.edge] * (FreeGroup.mk c.replacement)⁻¹) *
        (FreeGroup.mk c.before)⁻¹ *
        (FreeGroup.mk c.before * FreeGroup.mk c.replacement * FreeGroup.mk c.after) := by
      group
    _ = _ := by rw [he]; group

end FaceCollapse

/-- A tree terminal allows a nonempty freely trivial boundary. Thus singular
tree edges do not have to disappear by face removals. This is a certificate,
not an assertion that every area witness has such a certificate. -/
inductive Shelling (R : Finset Word) (K : Nat) : Word → Nat → Prop
  | tree (w : Word) (h : FreeGroup.mk w = 1) : Shelling R K w 0
  | face {w v : Word} {n : Nat} (c : FaceCollapse R K w v)
      (rest : Shelling R K v n) : Shelling R K w (n+1)

/-- The entire extraction/budget induction, conditional only on an explicit
shelling certificate. It supplies original relators, with exactly n factors. -/
theorem shelling_factors {R : Finset Word} {K : Nat} {w : Word} {n : Nat}
    (s : Shelling R K w n) :
    ∃ fs : List WordFactor, fs.length = n ∧ (∀ f∈fs, f.2.1∈R) ∧
      (fs.map wordFactorValue).prod = FreeGroup.mk w ∧
      ∀ f∈fs, f.1.length ≤ w.length + n*K := by
  induction s with
  | tree w h => exact ⟨[],rfl,by simp,by simpa using h.symm,by simp⟩
  | @face w v n c rest ih =>
    obtain ⟨fs,hlen,hmem,hprod,hshort⟩ := ih
    refine ⟨c.factor :: fs,by simp [hlen],?_,?_,?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact c.factor_mem
      · exact hmem f hf
    · simpa only [List.map_cons,List.prod_cons,hprod] using c.factor_value.symm
    · intro f hf
      have hv := c.boundary_length
      rcases List.mem_cons.mp hf with rfl | hf
      · have hc := c.factor_length
        apply hc.trans
        rw [Nat.add_mul,one_mul]
        omega
      · have hs := hshort f hf
        rw [Nat.add_mul,one_mul]
        omega

/-- Boundary free reduction costs no length. No completeness assertion about
arbitrary area witnesses is hidden in this adapter. -/
theorem factors_of_reduced_shelling (R : Finset Word) (K k : Nat) (w : Word)
    (h : ∃ n, n ≤ k ∧ Shelling R K (FreeGroup.reduce w) n) :
    ∃ fs : List WordFactor, fs.length ≤ k ∧ (∀ f∈fs, f.2.1∈R) ∧
      (fs.map wordFactorValue).prod = FreeGroup.mk w ∧
      ∀ f∈fs, f.1.length ≤ w.length + k*K := by
  obtain ⟨n,hn,s⟩ := h
  obtain ⟨fs,hlen,hmem,hprod,hshort⟩ := shelling_factors s
  refine ⟨fs,hlen.le.trans hn,hmem,?_,?_⟩
  · simpa only [FreeGroup.reduce.self] using hprod
  · intro f hf
    have hl := (FreeGroup.reduce.red (L := w)).length_le
    exact (hshort f hf).trans (Nat.add_le_add hl (Nat.mul_le_mul_right K hn))

/-- The zero-area case of the original statement, independent of shellings. -/
theorem zero_area (R : Finset Word) (w : Word) (h : finiteWordArea R w 0) :
    ∃ fs : List WordFactor, fs.length ≤ 0 ∧ (∀ f∈fs, f.2.1∈R) ∧
      (fs.map wordFactorValue).prod = FreeGroup.mk w ∧
      ∀ f∈fs, f.1.length ≤ w.length := by
  obtain ⟨fs,hlen,hmem,hprod⟩ := h
  have hf : fs = [] := List.length_eq_zero_iff.mp (by omega)
  subst fs
  exact ⟨[],by simp,by simp,hprod,by simp⟩

end Blueprint.ConjugatorCollapse
