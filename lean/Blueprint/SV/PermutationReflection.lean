import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic

namespace Blueprint.SV
noncomputable section

variable {α : Type*}

/-- Choose one base point on each orbit, including singleton orbits. -/
def orbitBase (p : Equiv.Perm α) (x : α) : α :=
  (Quotient.mk (Equiv.Perm.SameCycle.setoid p) x).out

theorem orbitBase_related (p : Equiv.Perm α) (x : α) : p.SameCycle (orbitBase p x) x :=
  @Quotient.exact α (Equiv.Perm.SameCycle.setoid p) _ x
    (Quotient.out_eq (Quotient.mk (Equiv.Perm.SameCycle.setoid p) x))

theorem orbitBase_eq (p : Equiv.Perm α) {x y : α} (h : p.SameCycle x y) :
    orbitBase p x = orbitBase p y := by
  unfold orbitBase
  rw [Quotient.sound h]

def orbitCoordinate (p : Equiv.Perm α) (x : α) : ℤ :=
  Classical.choose (orbitBase_related p x)

theorem orbitCoordinate_spec (p : Equiv.Perm α) (x : α) :
    (p ^ orbitCoordinate p x) (orbitBase p x) = x :=
  Classical.choose_spec (orbitBase_related p x)

/-- Reflection of each orbit about its chosen base point. No finiteness is needed. -/
def orbitReflection (p : Equiv.Perm α) (x : α) : α :=
  (p ^ (-orbitCoordinate p x)) (orbitBase p x)

theorem inverse_power_well_defined (p : Equiv.Perm α) (x : α) (a b : ℤ)
    (h : (p ^ a) x = (p ^ b) x) : (p ^ (-a)) x = (p ^ (-b)) x := by
  have hh := congrArg (p ^ (-a-b)) h
  simp only [←Equiv.Perm.mul_apply, ←zpow_add] at hh
  have ha : -a-b+a = -b := by omega
  have hb : -a-b+b = -a := by omega
  simpa only [ha,hb] using hh.symm

theorem orbitReflection_at (p : Equiv.Perm α) (x : α) (n : ℤ)
    (h : (p ^ n) (orbitBase p x) = x) :
    orbitReflection p x = (p ^ (-n)) (orbitBase p x) :=
  inverse_power_well_defined p _ _ _ ((orbitCoordinate_spec p x).trans h.symm)

theorem orbitReflection_power (p : Equiv.Perm α) (x : α) (n : ℤ) :
    orbitReflection p ((p ^ n) x) = (p ^ (-n)) (orbitReflection p x) := by
  have hb : orbitBase p ((p ^ n) x) = orbitBase p x :=
    orbitBase_eq p (Equiv.Perm.SameCycle.rfl.zpow_left)
  have hx : (p ^ (n + orbitCoordinate p x)) (orbitBase p ((p ^ n) x)) = (p ^ n) x := by
    rw [hb,zpow_add,Equiv.Perm.mul_apply,orbitCoordinate_spec]
  rw [orbitReflection_at p _ _ hx,hb]
  simp only [orbitReflection,←Equiv.Perm.mul_apply,←zpow_add,neg_add]

theorem orbitReflection_involutive (p : Equiv.Perm α) : Function.Involutive (orbitReflection p) := by
  intro x
  have hb : orbitBase p (orbitReflection p x) = orbitBase p x := by
    apply orbitBase_eq p
    exact (Equiv.Perm.SameCycle.rfl.zpow_left).trans (orbitBase_related p x)
  have hx : (p ^ (-orbitCoordinate p x)) (orbitBase p (orbitReflection p x)) =
      orbitReflection p x := by rw [hb]; rfl
  rw [orbitReflection_at p _ _ hx,hb,neg_neg,orbitCoordinate_spec]

def reversingPermutation (p : Equiv.Perm α) : Equiv.Perm α :=
  ⟨orbitReflection p,orbitReflection p,orbitReflection_involutive p,orbitReflection_involutive p⟩

theorem reversingPermutation_square (p : Equiv.Perm α) :
    reversingPermutation p * reversingPermutation p = 1 := by
  ext x
  exact orbitReflection_involutive p x

theorem reversingPermutation_conjugates (p : Equiv.Perm α) :
    reversingPermutation p * p * reversingPermutation p = p⁻¹ := by
  ext x
  change orbitReflection p (p (orbitReflection p x)) = p⁻¹ x
  have hh := orbitReflection_power p (orbitReflection p x) 1
  simpa only [zpow_one,zpow_neg_one,orbitReflection_involutive p x] using hh

end
end Blueprint.SV

#print axioms Blueprint.SV.orbitBase
#print axioms Blueprint.SV.orbitBase_related
#print axioms Blueprint.SV.orbitBase_eq
#print axioms Blueprint.SV.orbitCoordinate
#print axioms Blueprint.SV.orbitCoordinate_spec
#print axioms Blueprint.SV.orbitReflection
#print axioms Blueprint.SV.inverse_power_well_defined
#print axioms Blueprint.SV.orbitReflection_at
#print axioms Blueprint.SV.orbitReflection_power
#print axioms Blueprint.SV.orbitReflection_involutive
#print axioms Blueprint.SV.reversingPermutation
#print axioms Blueprint.SV.reversingPermutation_square
#print axioms Blueprint.SV.reversingPermutation_conjugates
