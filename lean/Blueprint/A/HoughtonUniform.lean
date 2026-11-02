import Blueprint.A.HoughtonHalving
import Mathlib.Data.Nat.Log

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 1000000

def uniformFarCap (M : Nat) : Nat := dyadicCap (Nat.clog 2 M-1)-4

theorem clog_two_pos (M : Nat) (hM : 2≤M) : 0<Nat.clog 2 M := by
  apply (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr
  simpa only [pow_zero] using (by omega : 1<M)

/-- Uniform finite area witnesses up to M, at the exact first bound of the
paper's far-commutator proposition. Its ceiling logarithm is Nat.clog 2 M. -/
theorem far_uniform_area (M : Nat) (hM : 2≤M) (n : Nat) (hn : 2≤n) (hnM : n≤M) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ n)) (uniformFarCap M) := by
  have hp := clog_two_pos M hM
  have he : Nat.clog 2 M-1+1=Nat.clog 2 M := by omega
  have hb : n≤2^(Nat.clog 2 M-1+1) := by
    rw [he]
    exact le_trans hnM (Nat.le_pow_clog (by decide : 1<2) M)
  have h := farAreaBound_dyadic (Nat.clog 2 M-1) n hn hb
  apply area_weaken (far_commutator_area n hn)
  dsimp [uniformFarCap]
  omega

theorem uniformFarCap_eq (M : Nat) (hM : 2≤M) :
    uniformFarCap M=5*3^(Nat.clog 2 M-1)*2^(Nat.clog 2 M*(Nat.clog 2 M-1))-4 := by
  have hp := clog_two_pos M hM
  have he : Nat.clog 2 M-1+1=Nat.clog 2 M := by omega
  simp only [uniformFarCap,dyadicCap,he,Nat.mul_comm (Nat.clog 2 M-1) (Nat.clog 2 M)]

theorem far_uniform_translate_area (M : Nat) (hM : 2≤M) (i : ℤ) (n : Nat)
    (hn : 2≤n) (hnM : n≤M) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ i) (sigmaZ (i+n))) (uniformFarCap M) := by
  apply far_area_translate
  convert far_uniform_area M hM n hn hnM using 1
  congr 2
  omega

theorem far_commutator_exact_dyadic (M : Nat) (hM : 2≤M) :
    ∀ n : Nat, 2≤n → n≤M →
      FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ n))
        (5*3^(Nat.clog 2 M-1)*2^(Nat.clog 2 M*(Nat.clog 2 M-1))-4) := by
  intro n hn hnM
  simpa only [uniformFarCap_eq M hM] using far_uniform_area M hM n hn hnM

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.uniformFarCap
#print axioms Blueprint.HoughtonProof.clog_two_pos
#print axioms Blueprint.HoughtonProof.far_uniform_area
#print axioms Blueprint.HoughtonProof.uniformFarCap_eq
#print axioms Blueprint.HoughtonProof.far_uniform_translate_area
#print axioms Blueprint.HoughtonProof.far_commutator_exact_dyadic
