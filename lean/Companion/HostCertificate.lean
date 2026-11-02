import Companion.Configuration

namespace Companion.Concrete

structure AffineRow where
  constant : Bool
  sources : List Point
  deriving DecidableEq, Repr

def rowValue (r : AffineRow) (v : Config) : Bool := r.constant ^^ parity (bit v) r.sources
def rowAdd (a b : AffineRow) : AffineRow :=
  ⟨a.constant ^^ b.constant,xorLists a.sources b.sources⟩

theorem rowValue_add (a b : AffineRow) (v : Config) :
    rowValue (rowAdd a b) v = (rowValue a v ^^ rowValue b v) := by
  simp only [rowValue,rowAdd,parity_xorLists]
  cases a.constant <;> cases b.constant <;>
    cases parity (bit v) a.sources <;> cases parity (bit v) b.sources <;> rfl

def hostRow : List HostLetter → Point → AffineRow
  | [],y => ⟨false,[y]⟩
  | .p::w,y => hostRow w (pBackward y)
  | .pinv::w,y => hostRow w (pForward y)
  | .q::w,y => hostRow w (qBackward y)
  | .qinv::w,y => hostRow w (qForward y)
  | .i::w,y => hostRow w (swapPoint y)
  | .t::w,y => let r := hostRow w y; ⟨r.constant ^^ decide (y=origin),r.sources⟩
  | .d::w,y => if y=next then rowAdd (hostRow w y) (hostRow w origin) else hostRow w y

theorem hostRow_sound (w : List HostLetter) (v : Config) (y : Point) :
    bit (hostEval w v) y = rowValue (hostRow w y) v := by
  induction w generalizing y with
  | nil => simp [hostEval,hostRow,rowValue,parity]
  | cons a w ih =>
    cases a
    · simpa only [hostEval,Equiv.Perm.mul_apply,hostGenerator,bit_mapConfig,pPoint,
        Equiv.symm_mk,Equiv.coe_fn_mk,hostRow] using ih (pBackward y)
    · simpa only [hostEval,Equiv.Perm.mul_apply,hostGenerator,bit_mapConfig,pPoint,
        Equiv.symm_symm,Equiv.coe_fn_mk,hostRow] using ih (pForward y)
    · simpa only [hostEval,Equiv.Perm.mul_apply,hostGenerator,bit_mapConfig,qPoint,
        Equiv.symm_mk,Equiv.coe_fn_mk,hostRow] using ih (qBackward y)
    · simpa only [hostEval,Equiv.Perm.mul_apply,hostGenerator,bit_mapConfig,qPoint,
        Equiv.symm_symm,Equiv.coe_fn_mk,hostRow] using ih (qForward y)
    · simpa only [hostEval,Equiv.Perm.mul_apply,hostGenerator,bit_mapConfig,iPoint,
        Equiv.symm_mk,Equiv.coe_fn_mk,hostRow] using ih (swapPoint y)
    · change bit (flipConfig origin (hostEval w v)) y = _
      rw [bit_flipConfig,ih]
      simp only [hostRow,rowValue]
      cases (hostRow w y).constant <;> cases parity (bit v) (hostRow w y).sources <;>
        cases decide (y=origin) <;> rfl
    · change bit (dConfig (hostEval w v)) y = _
      rw [bit_dConfig,ih,ih]
      by_cases hy : y=next
      · simp [hostRow,hy,rowValue_add]
      · simp [hostRow,hy]

def move : HostLetter → Point → Point
  | .p => pBackward
  | .pinv => pForward
  | .q => qBackward
  | .qinv => qForward
  | .i => swapPoint
  | .t | .d => id

def shift (k : Nat) (y : Point) : Point := (y.1,y.2+k)

theorem move_height (a : HostLetter) (y : Point) : y.2 ≤ (move a y).2+1 := by
  rcases y with ⟨r,h⟩
  cases a <;> cases r <;> cases h <;> simp [move,pBackward,pForward,qBackward,qForward,swapPoint] <;> omega

theorem move_shift (a : HostLetter) (y : Point) (k : Nat) (hy : 0<y.2) :
    move a (shift k y) = shift k (move a y) := by
  rcases y with ⟨r,h⟩
  cases h with
  | zero => simp at hy
  | succ h =>
    cases a <;> cases r <;>
      simp [move,shift,pBackward,pForward,qBackward,qForward,swapPoint,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def travel : List HostLetter → Point → Point
  | [],y => y
  | a::w,y => travel w (move a y)

theorem travel_shift (w : List HostLetter) (y : Point) (k : Nat)
    (hy : w.length+1≤y.2) : travel w (shift k y) = shift k (travel w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih =>
    have hh := move_height a y
    have hp : 0<y.2 := by simp only [List.length_cons] at hy; omega
    simp only [travel,move_shift a y k hp]
    apply ih
    simp only [List.length_cons] at hy
    omega

theorem hostRow_high (w : List HostLetter) (y : Point) (hy : w.length+2≤y.2) :
    hostRow w y = ⟨false,[travel w y]⟩ := by
  induction w generalizing y with
  | nil => rfl
  | cons a w ih =>
    have hh := move_height a y
    have hb : w.length+2≤(move a y).2 := by simp only [List.length_cons] at hy; omega
    have hn : y≠next := by intro h; subst y; simp [next] at hy
    have ho : y≠origin := by intro h; subst y; simp [origin] at hy
    cases a
    all_goals simp only [hostRow,travel,move] at *
    all_goals first
      | exact ih _ hb
      | (rw [ih y (by simp only [List.length_cons] at hy; omega)]; simp [ho,hn])

def shiftRow (k : Nat) (r : AffineRow) : AffineRow := ⟨r.constant,r.sources.map (shift k)⟩

theorem hostRow_shift (w : List HostLetter) (y : Point) (k : Nat)
    (hy : w.length+2≤y.2) : hostRow w (shift k y) = shiftRow k (hostRow w y) := by
  rw [hostRow_high w y hy,hostRow_high w (shift k y) (by simp only [shift]; omega)]
  rw [travel_shift w y k (by omega)]
  rfl

def rays : List Ray := [.one,.two,.three]
def boundedHostCheck (w : List HostLetter) : Bool := rays.all fun r =>
  (List.range (w.length+3)).all fun h => decide (hostRow w (r,h)=⟨false,[(r,h)]⟩)

theorem boundedHostCheck_rows {w : List HostLetter} (hc : boundedHostCheck w=true)
    (y : Point) : hostRow w y=⟨false,[y]⟩ := by
  have low (r : Ray) (h : Nat) (hh : h<w.length+3) : hostRow w (r,h)=⟨false,[(r,h)]⟩ := by
    have hr : r ∈ rays := by cases r <;> simp [rays]
    have hi := List.all_eq_true.mp (List.all_eq_true.mp hc r hr) h (List.mem_range.mpr hh)
    exact of_decide_eq_true hi
  by_cases hy : y.2<w.length+3
  · exact low y.1 y.2 hy
  · let base : Point := (y.1,w.length+2)
    let k := y.2-(w.length+2)
    have he : shift k base=y := by
      apply Prod.ext <;> simp [shift,k,base] <;> omega
    rw [← he,hostRow_shift w base k (by simp [base])]
    rw [low y.1 (w.length+2) (by omega)]
    rfl

/-- Sound on the infinite three-ray space; no test bound is assumed as a hypothesis. -/
theorem boundedHostCheck_sound {w : List HostLetter} (hc : boundedHostCheck w=true) : hostEval w=1 := by
  apply Equiv.ext
  intro v
  apply Finset.ext
  intro y
  change y ∈ hostEval w v ↔ y ∈ v
  have h := hostRow_sound w v y
  rw [boundedHostCheck_rows hc y] at h
  simp only [rowValue,parity,Bool.xor_false,Bool.false_xor] at h
  constructor
  · intro hv
    have hb : bit (hostEval w v) y=true := by simp [bit,hv]
    rw [h] at hb
    simpa [bit] using hb
  · intro hv
    have hb : bit v y=true := by simp [bit,hv]
    rw [← h] at hb
    simpa [bit] using hb

end Companion.Concrete
