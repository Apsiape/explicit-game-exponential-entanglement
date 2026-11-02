import Blueprint.A.AreaCalculus

namespace Blueprint.PairProof
open Companion
open ASector

def Close {α ι : Type} (R : ι → FreeGroup α) (a b : FreeGroup α) (k : Nat) : Prop :=
  FiniteArea.Area R (a*b⁻¹) k

theorem close_refl {α ι : Type} (R : ι → FreeGroup α) (a : FreeGroup α) : Close R a a 0 := by
  simpa only [Close,mul_inv_cancel] using area_one R 0

theorem close_weaken {α ι : Type} {R : ι → FreeGroup α} {a b : FreeGroup α} {k l : Nat}
    (h : Close R a b k) (hkl : k≤l) : Close R a b l := area_weaken h hkl

theorem close_symm {α ι : Type} {R : ι → FreeGroup α} {a b : FreeGroup α} {k : Nat}
    (h : Close R a b k) : Close R b a k := by
  simpa [Close,mul_inv_rev] using area_inv h

theorem close_trans {α ι : Type} {R : ι → FreeGroup α} {a b c : FreeGroup α} {k l : Nat}
    (h : Close R a b k) (g : Close R b c l) : Close R a c (k+l) := by
  have hh := area_mul h g
  simpa [Close,mul_assoc] using hh

theorem close_mul {α ι : Type} {R : ι → FreeGroup α} {a b c d : FreeGroup α} {k l : Nat}
    (h : Close R a b k) (g : Close R c d l) : Close R (a*c) (b*d) (k+l) := by
  have hh := area_mul h (area_conj b g)
  convert hh using 1
  dsimp [Close]
  group

theorem close_left {α ι : Type} {R : ι → FreeGroup α} {a b : FreeGroup α} {k : Nat}
    (c : FreeGroup α) (h : Close R a b k) : Close R (c*a) (c*b) k := by
  have hh := close_mul (close_refl R c) h
  simpa only [Nat.zero_add] using hh

theorem close_right {α ι : Type} {R : ι → FreeGroup α} {a b : FreeGroup α} {k : Nat}
    (c : FreeGroup α) (h : Close R a b k) : Close R (a*c) (b*c) k := by
  have hh := close_mul h (close_refl R c)
  simpa only [Nat.add_zero] using hh

theorem close_inv {α ι : Type} {R : ι → FreeGroup α} {a b : FreeGroup α} {k : Nat}
    (h : Close R a b k) : Close R a⁻¹ b⁻¹ k := by
  have hh := area_conj a⁻¹ (area_inv h)
  convert hh using 1
  dsimp [Close]
  group

theorem close_conj {α ι : Type} {R : ι → FreeGroup α} {a b : FreeGroup α} {k : Nat}
    (c : FreeGroup α) (h : Close R a b k) : Close R (c*a*c⁻¹) (c*b*c⁻¹) k :=
  close_right c⁻¹ (close_left c h)

theorem close_comm {α ι : Type} {R : ι → FreeGroup α} {a b c d : FreeGroup α} {k l : Nat}
    (h : Close R a b k) (g : Close R c d l) :
    Close R (groupComm a c) (groupComm b d) (2*k+2*l) := by
  have hh := close_mul (close_mul (close_mul h g) (close_inv h)) (close_inv g)
  simpa only [groupComm,show k+l+k+l=2*k+2*l by omega] using hh

theorem close_conjugator {α ι : Type} {R : ι → FreeGroup α} {a b : FreeGroup α} {k : Nat}
    (z : FreeGroup α) (h : Close R a b k) : Close R (a*z*a⁻¹) (b*z*b⁻¹) (2*k) := by
  have hh := close_mul (close_right z h) (close_inv h)
  simpa only [two_mul] using hh

theorem close_to_one {α ι : Type} {R : ι → FreeGroup α} {a : FreeGroup α} {k : Nat} :
    Close R a 1 k ↔ FiniteArea.Area R a k := by simp only [Close,inv_one,mul_one]

theorem close_product {α ι κ : Type} {R : ι → FreeGroup α}
    (xs : List κ) (a b : κ → FreeGroup α) (k : Nat)
    (h : ∀ i∈xs, Close R (a i) (b i) k) :
    Close R (xs.map a).prod (xs.map b).prod (xs.length*k) := by
  induction xs with
  | nil => simpa using close_refl R 1
  | cons i xs ih =>
    have hh := close_mul (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))
    simpa only [List.map_cons,List.prod_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hh

end Blueprint.PairProof

#print axioms Blueprint.PairProof.Close
#print axioms Blueprint.PairProof.close_refl
#print axioms Blueprint.PairProof.close_weaken
#print axioms Blueprint.PairProof.close_symm
#print axioms Blueprint.PairProof.close_trans
#print axioms Blueprint.PairProof.close_mul
#print axioms Blueprint.PairProof.close_left
#print axioms Blueprint.PairProof.close_right
#print axioms Blueprint.PairProof.close_inv
#print axioms Blueprint.PairProof.close_conj
#print axioms Blueprint.PairProof.close_comm
#print axioms Blueprint.PairProof.close_conjugator
#print axioms Blueprint.PairProof.close_to_one
#print axioms Blueprint.PairProof.close_product
