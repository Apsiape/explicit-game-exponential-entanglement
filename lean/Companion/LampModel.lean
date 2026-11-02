import Companion.HostCertificate

namespace Companion.Concrete

abbrev Register := Config → Bool
abbrev Sample := Bool × Register

def flipRegister (site : Config) (q : Register) : Register :=
  fun v => q v ^^ decide (v=site)

def xAt (site : Config) : Equiv.Perm Sample where
  toFun s := (s.1,flipRegister site s.2)
  invFun s := (s.1,flipRegister site s.2)
  left_inv := by rintro ⟨c,q⟩; apply Prod.ext; rfl; funext v; simp [flipRegister,Bool.xor_assoc]
  right_inv := by rintro ⟨c,q⟩; apply Prod.ext; rfl; funext v; simp [flipRegister,Bool.xor_assoc]

def zAt (site : Config) : Equiv.Perm Sample where
  toFun s := (s.1 ^^ s.2 site,s.2)
  invFun s := (s.1 ^^ s.2 site,s.2)
  left_inv := by rintro ⟨c,q⟩; simp [Bool.xor_assoc]
  right_inv := by rintro ⟨c,q⟩; simp [Bool.xor_assoc]

def hostLift (h : Equiv.Perm Config) : Equiv.Perm Sample where
  toFun s := (s.1,s.2 ∘ h.symm)
  invFun s := (s.1,s.2 ∘ h)
  left_inv := by rintro ⟨c,q⟩; apply Prod.ext; rfl; funext v; simp
  right_inv := by rintro ⟨c,q⟩; apply Prod.ext; rfl; funext v; simp

theorem hostLift_mul (g h : Equiv.Perm Config) : hostLift (g*h)=hostLift g*hostLift h := by
  apply Equiv.ext
  rintro ⟨c,q⟩
  rfl

inductive Letter where
  | host (a : HostLetter)
  | x | z | unit
  deriving DecidableEq, Repr

def generator : Letter → Equiv.Perm Sample
  | .host a => hostLift (hostGenerator a)
  | .x => xAt ∅
  | .z => zAt ∅
  | .unit => 1

def evalLetters : List Letter → Equiv.Perm Sample
  | [] => 1
  | a::w => generator a * evalLetters w

structure NormalForm where
  phase : Bool
  xs : List Config
  zs : List Config
  host : List HostLetter
  deriving DecidableEq

def lampAction (c : Bool) (xs zs : List Config) (s : Sample) : Sample :=
  (s.1 ^^ c ^^ parity s.2 zs,fun v => s.2 v ^^ parity (fun u => decide (v=u)) xs)

def normalAction (n : NormalForm) (s : Sample) : Sample :=
  lampAction n.phase n.xs n.zs (hostLift (hostEval n.host) s)

def prepend : Letter → NormalForm → NormalForm
  | .host a,n =>
      ⟨n.phase,n.xs.map (hostGenerator a),n.zs.map (hostGenerator a),a::n.host⟩
  | .x,n => ⟨n.phase,toggle ∅ n.xs,n.zs,n.host⟩
  | .z,n => ⟨n.phase ^^ parity (fun u => decide (∅=u)) n.xs,n.xs,toggle ∅ n.zs,n.host⟩
  | .unit,n => n

def normalForm : List Letter → NormalForm
  | [] => ⟨false,[],[],[]⟩
  | a::w => prepend a (normalForm w)

theorem parity_congr {α : Type*} {f g : α → Bool} (h : ∀ a, f a=g a) (ls : List α) :
    parity f ls=parity g ls := by
  induction ls with
  | nil => rfl
  | cons a as ih => simp [parity,h a,ih]

theorem lampAction_host (h : Equiv.Perm Config) (c : Bool) (xs zs : List Config) (s : Sample) :
    hostLift h (lampAction c xs zs s) =
      lampAction c (xs.map h) (zs.map h) (hostLift h s) := by
  apply Prod.ext
  · change (s.1 ^^ c ^^ parity s.2 zs) = (s.1 ^^ c ^^ parity (s.2 ∘ h.symm) (zs.map h))
    rw [parity_map]
    congr 2
    funext v
    simp
  · funext v
    change (s.2 (h.symm v) ^^ parity (fun u => decide (h.symm v=u)) xs) =
      (s.2 (h.symm v) ^^ parity (fun u => decide (v=u)) (xs.map h))
    rw [parity_map]
    congr 1
    apply parity_congr
    intro u
    simp only [Function.comp_apply]
    congr 1
    exact propext h.symm_apply_eq

theorem normalAction_prepend (a : Letter) (n : NormalForm) (s : Sample) :
    normalAction (prepend a n) s = generator a (normalAction n s) := by
  cases a with
  | unit => rfl
  | host a =>
    simp only [normalAction,prepend,hostEval,hostLift_mul,Equiv.Perm.mul_apply,generator]
    exact (lampAction_host _ _ _ _ _).symm
  | x =>
    apply Prod.ext
    · rfl
    · funext v
      simp only [normalAction,prepend,lampAction,generator,xAt,Equiv.coe_fn_mk,flipRegister,
        parity_toggle]
      cases (hostLift (hostEval n.host) s).2 v <;>
        cases parity (fun u => decide (v=u)) n.xs <;> cases decide (v=∅) <;> rfl
  | z =>
    apply Prod.ext
    · simp only [normalAction,prepend,lampAction,generator,zAt,Equiv.coe_fn_mk,parity_toggle]
      cases (hostLift (hostEval n.host) s).1 <;> cases n.phase <;>
        cases parity (fun u => decide (∅=u)) n.xs <;>
        cases (hostLift (hostEval n.host) s).2 ∅ <;>
        cases parity (hostLift (hostEval n.host) s).2 n.zs <;> rfl
    · rfl

theorem normalForm_sound (w : List Letter) (s : Sample) :
    evalLetters w s = normalAction (normalForm w) s := by
  induction w with
  | nil =>
    apply Prod.ext
    · simp [evalLetters,normalAction,normalForm,lampAction,hostLift,hostEval,parity]
    · funext v
      simp [evalLetters,normalAction,normalForm,lampAction,hostLift,hostEval,parity] <;> rfl
  | cons a w ih =>
    rw [normalForm,normalAction_prepend,evalLetters,Equiv.Perm.mul_apply,ih]

def decode (includeI : Bool) (a : Nat × Bool) : Letter :=
  match a.1 with
  | 1 => .host (if a.2 then .p else .pinv)
  | 2 => .host (if a.2 then .q else .qinv)
  | 3 => .host .t
  | 4 => .host .d
  | 5 => .x
  | 6 => .z
  | 7 => if includeI then .host .i else .unit
  | _ => .unit

def baseGenerator (includeI : Bool) (j : Nat) : Equiv.Perm Sample := generator (decode includeI (j,true))
def wordHom (includeI : Bool) : FreeGroup Nat →* Equiv.Perm Sample := FreeGroup.lift (baseGenerator includeI)
def wordPermutation (includeI : Bool) (w : Word) : Equiv.Perm Sample := wordHom includeI (FreeGroup.mk w)

theorem decode_inverse (includeI : Bool) (a : Nat × Bool) :
    generator (decode includeI a) = if a.2 then baseGenerator includeI a.1 else (baseGenerator includeI a.1)⁻¹ := by
  rcases a with ⟨j,b⟩
  rcases j with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | j)))))))
  all_goals cases b <;> cases includeI <;> rfl

theorem wordPermutation_eval (includeI : Bool) (w : Word) :
    wordPermutation includeI w = evalLetters (w.map (decode includeI)) := by
  induction w with
  | nil => simp [wordPermutation,wordHom,FreeGroup.lift_mk,evalLetters]
  | cons a w ih =>
    simp only [wordPermutation,wordHom,FreeGroup.lift_mk,List.map_cons,List.prod_cons,
      evalLetters,decode_inverse] at *
    rw [ih]
    cases a.2 <;> rfl

def GP : Subgroup (Equiv.Perm Sample) := (wordHom false).range
def GPplus : Subgroup (Equiv.Perm Sample) := (wordHom true).range

def wordIdentityCheck (includeI : Bool) (w : Word) : Bool :=
  let n := normalForm (w.map (decode includeI))
  decide (n.phase=false ∧ n.xs=[] ∧ n.zs=[]) && boundedHostCheck n.host

theorem wordIdentityCheck_sound {includeI : Bool} {w : Word}
    (hc : wordIdentityCheck includeI w=true) : wordPermutation includeI w=1 := by
  simp only [wordIdentityCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  apply Equiv.ext
  intro s
  rw [wordPermutation_eval,normalForm_sound]
  simp only [normalAction,hc.1.1,hc.1.2.1,hc.1.2.2,boundedHostCheck_sound hc.2]
  apply Prod.ext
  · simp [lampAction,hostLift,parity]
  · funext v; simp [lampAction,hostLift,parity] <;> rfl

end Companion.Concrete
