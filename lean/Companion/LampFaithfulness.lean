import Companion.LampModel

namespace Companion.Concrete

theorem parity_false {α : Type*} (ls : List α) : parity (fun _ => false) ls=false := by
  induction ls with
  | nil => rfl
  | cons a as ih => simp [parity,ih]

theorem parity_indicator {α : Type*} [DecidableEq α] (ls : List α) (hn : ls.Nodup) (v : α) :
    parity (fun u => decide (v=u)) ls=decide (v ∈ ls) := by
  induction ls with
  | nil => rfl
  | cons a as ih =>
    have hna := (List.nodup_cons.mp hn).1
    have hns := (List.nodup_cons.mp hn).2
    rw [parity,ih hns]
    by_cases hv : v=a
    · subst v; simp [hna]
    · simp [hv]

theorem list_empty_of_parities {α : Type*} [DecidableEq α] (ls : List α) (hn : ls.Nodup)
    (hz : ∀ v, parity (fun u => decide (v=u)) ls=false) : ls=[] := by
  cases ls with
  | nil => rfl
  | cons a as =>
    have h := hz a
    rw [parity_indicator _ hn] at h
    simp at h

/-- Canonical finite Pauli coordinates and the affine action are recovered
from the concrete permutation. This rules out an artificial quotient model. -/
theorem normalAction_faithful (n : NormalForm) (hx : n.xs.Nodup) (hz : n.zs.Nodup)
    (h : ∀ s, normalAction n s=s) :
    n.phase=false ∧ n.xs=[] ∧ n.zs=[] ∧ hostEval n.host=1 := by
  have hc : n.phase=false := by
    have he := congrArg Prod.fst (h (false,fun _ => false))
    simpa [normalAction,lampAction,hostLift,parity_false] using he
  have hxs : n.xs=[] := by
    apply list_empty_of_parities _ hx
    intro v
    have he := congrFun (congrArg Prod.snd (h (false,fun _ => false))) v
    simpa [normalAction,lampAction,hostLift] using he
  have hhInv (v : Config) : (hostEval n.host).symm v=v := by
    have he := congrFun (congrArg Prod.snd (h (false,fun u => decide (u=v)))) v
    simpa [normalAction,lampAction,hostLift,hxs,parity] using he
  have hh : hostEval n.host=1 := by
    apply Equiv.ext
    intro v
    have he := hhInv (hostEval n.host v)
    simpa using he.symm
  have hzs : n.zs=[] := by
    apply list_empty_of_parities _ hz
    intro v
    have he := congrArg Prod.fst (h (false,fun u => decide (v=u)))
    simp only [normalAction,lampAction,hh,hc,hostLift,Equiv.coe_fn_mk,Prod.fst,Prod.snd,
      Bool.false_xor] at he
    exact he
  exact ⟨hc,hxs,hzs,hh⟩

def jWord : Word := [(5,true),(6,true),(5,true),(6,true)]
theorem j_normal (b : Bool) : normalForm (jWord.map (decode b))=⟨true,[],[],[]⟩ := by
  cases b <;> decide +kernel

theorem j_action_phase (b : Bool) (s : Sample) : (wordPermutation b jWord s).1 = !s.1 := by
  rw [wordPermutation_eval,normalForm_sound,j_normal]
  change (s.1 ^^ true ^^ false) = !s.1
  cases s.1 <;> rfl

def phaseFlip (s : Sample) : Sample := (!s.1,s.2)
theorem j_action (b : Bool) (s : Sample) : wordPermutation b jWord s=phaseFlip s := by
  rw [wordPermutation_eval,normalForm_sound,j_normal]
  apply Prod.ext
  · change (s.1 ^^ true ^^ false) = !s.1
    cases s.1 <;> rfl
  · funext v
    simp [normalAction,lampAction,hostLift,hostEval,parity,phaseFlip] <;> rfl

theorem generator_phaseFlip (a : Letter) (s : Sample) : generator a (phaseFlip s)=phaseFlip (generator a s) := by
  cases a with
  | host a => rfl
  | unit => rfl
  | x => rfl
  | z =>
    apply Prod.ext
    · change ((!s.1) ^^ s.2 ∅) = !(s.1 ^^ s.2 ∅)
      cases s.1 <;> cases s.2 ∅ <;> rfl
    · rfl

theorem evalLetters_phaseFlip (w : List Letter) (s : Sample) :
    evalLetters w (phaseFlip s)=phaseFlip (evalLetters w s) := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [evalLetters,Equiv.Perm.mul_apply,ih,generator_phaseFlip]; rfl

theorem j_commutes_word (b : Bool) (w : Word) : Commute (wordPermutation b jWord) (wordPermutation b w) := by
  apply Equiv.ext
  intro s
  change wordPermutation b jWord (wordPermutation b w s)=wordPermutation b w (wordPermutation b jWord s)
  rw [j_action,j_action,wordPermutation_eval,evalLetters_phaseFlip]

theorem j_nontrivial (b : Bool) : wordPermutation b jWord≠1 := by
  intro h
  have he := congrArg (fun f : Equiv.Perm Sample => (f (false,fun _ => false)).1) h
  rw [j_action_phase] at he
  change true=false at he
  cases he

end Companion.Concrete
