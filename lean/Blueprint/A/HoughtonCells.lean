import Blueprint.A.HoughtonComparison

namespace Blueprint.HoughtonProof
noncomputable section
open Companion ASector Published PairProof
set_option maxHeartbeats 800000

def johnsonP : FreeGroup (Fin 3) := FreeGroup.of 0
def johnsonQ : FreeGroup (Fin 3) := FreeGroup.of 1
def johnsonAlpha : FreeGroup (Fin 3) := FreeGroup.of 2
def sigmaZ (j : ℤ) : FreeGroup (Fin 3) := johnsonP^j*johnsonAlpha*(johnsonP^j)⁻¹
def etaZ (j : ℤ) : FreeGroup (Fin 3) := johnsonP^j*(johnsonQ⁻¹*johnsonP)*(johnsonP^j)⁻¹

theorem johnson_relator_area (i : Fin 5) :
    FiniteArea.Area johnsonFiniteRelator (johnsonFiniteRelator i) 1 := by
  exact ⟨[(1,i,true)],by simp,by simp [FiniteArea.factorValue]⟩

theorem sigmaZ_zero : sigmaZ 0=johnsonAlpha := by simp [sigmaZ]

theorem etaZ_zero : etaZ 0=johnsonQ⁻¹*johnsonP := by simp [etaZ]

theorem sigmaZ_shift (j k : ℤ) :
    sigmaZ (j+k)=johnsonP^j*sigmaZ k*(johnsonP^j)⁻¹ := by
  simp only [sigmaZ,zpow_add]
  group

theorem etaZ_shift (j k : ℤ) :
    etaZ (j+k)=johnsonP^j*etaZ k*(johnsonP^j)⁻¹ := by
  simp only [etaZ,zpow_add]
  group

theorem johnson_alpha_square :
    FiniteArea.Area johnsonFiniteRelator (johnsonAlpha*johnsonAlpha) 1 := by
  convert johnson_relator_area 0 using 1 <;> decide +kernel

theorem sigmaZ_square (j : ℤ) :
    FiniteArea.Area johnsonFiniteRelator (sigmaZ j*sigmaZ j) 1 := by
  have h := area_conj (johnsonP^j) johnson_alpha_square
  convert h using 1
  dsimp [sigmaZ]
  group

theorem sigmaZ_inverse_close (j : ℤ) :
    Close johnsonFiniteRelator (sigmaZ j)⁻¹ (sigmaZ j) 1 := by
  simpa [Close,mul_inv_rev] using area_inv (sigmaZ_square j)

/-- Appendix A, cell (c1), with an explicit one-cell certificate. -/
theorem alpha_eta_area :
    FiniteArea.Area johnsonFiniteRelator (groupComm johnsonAlpha (etaZ 0)) 1 := by
  refine ⟨[(johnsonQ⁻¹,4,false)],by simp,?_⟩
  decide +kernel

/-- The two orientations of Appendix A's cell (c2). -/
theorem johnson_pq_close :
    Close johnsonFiniteRelator (johnsonP*johnsonQ*johnsonP⁻¹)
      (johnsonAlpha*johnsonQ) 1 := by
  change FiniteArea.Area johnsonFiniteRelator
    ((johnsonP*johnsonQ*johnsonP⁻¹)*(johnsonAlpha*johnsonQ)⁻¹) 1
  convert johnson_relator_area 3 using 1 <;> decide +kernel

theorem johnson_qp_close :
    Close johnsonFiniteRelator (johnsonQ*johnsonP*johnsonQ⁻¹)
      (johnsonAlpha⁻¹*johnsonP) 1 := by
  refine ⟨[(johnsonAlpha⁻¹,3,false)],by simp,?_⟩
  decide +kernel

theorem alpha_sigma_two_area :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ 0) (sigmaZ 2)) 1 := by
  convert johnson_relator_area 2 using 1 <;> decide +kernel

/-- Appendix A, cell (c3), at every integer translate. -/
theorem sigmaZ_distance_two (j : ℤ) :
    FiniteArea.Area johnsonFiniteRelator (groupComm (sigmaZ j) (sigmaZ (j+2))) 1 := by
  have h := area_conj (johnsonP^j) alpha_sigma_two_area
  convert h using 1
  rw [sigmaZ_shift j 2,←show sigmaZ (j+0)=sigmaZ j by simp,sigmaZ_shift j 0]
  dsimp [groupComm]
  group

theorem alpha_sigma_one_cube :
    FiniteArea.Area johnsonFiniteRelator ((sigmaZ 0*sigmaZ 1)^3) 1 := by
  convert johnson_relator_area 1 using 1 <;> decide +kernel

/-- Three inverse-to-positive replacements followed by one braid relator. -/
theorem sigmaZ_braid_zero :
    FiniteArea.Area johnsonFiniteRelator
      (sigmaZ 0*sigmaZ 1*sigmaZ 0*(sigmaZ 1)⁻¹*(sigmaZ 0)⁻¹*(sigmaZ 1)⁻¹) 4 := by
  have h0 := sigmaZ_inverse_close 0
  have h1 := sigmaZ_inverse_close 1
  have h := close_mul (close_mul (close_left (sigmaZ 0*sigmaZ 1*sigmaZ 0) h1) h0) h1
  have hc : Close johnsonFiniteRelator
      (sigmaZ 0*sigmaZ 1*sigmaZ 0*(sigmaZ 1)⁻¹*(sigmaZ 0)⁻¹*(sigmaZ 1)⁻¹)
      ((sigmaZ 0*sigmaZ 1)^3) 3 := by
    convert h using 1 <;> simp [pow_succ,mul_assoc]
  exact close_to_one.mp (close_trans hc (close_to_one.mpr alpha_sigma_one_cube))

theorem sigmaZ_braid (j : ℤ) :
    FiniteArea.Area johnsonFiniteRelator
      (sigmaZ j*sigmaZ (j+1)*sigmaZ j*(sigmaZ (j+1))⁻¹*(sigmaZ j)⁻¹*(sigmaZ (j+1))⁻¹) 4 := by
  have h := area_conj (johnsonP^j) sigmaZ_braid_zero
  convert h using 1
  rw [sigmaZ_shift j 1,←show sigmaZ (j+0)=sigmaZ j by simp,sigmaZ_shift j 0]
  group

/-- The one-cell transporter step used in Lee's recursion (i). -/
theorem etaZ_step_zero :
    Close johnsonFiniteRelator (etaZ 0) (etaZ 1*sigmaZ (-1)) 1 := by
  refine ⟨[(johnsonQ⁻¹*johnsonAlpha⁻¹,3,true)],by simp,?_⟩
  decide +kernel

theorem etaZ_step (k : ℤ) :
    Close johnsonFiniteRelator (etaZ k) (etaZ (k+1)*sigmaZ (k-1)) 1 := by
  have h := close_conj (johnsonP^k) etaZ_step_zero
  have hp : johnsonP^k*(etaZ 1*sigmaZ (-1))*(johnsonP^k)⁻¹ =
      (johnsonP^k*etaZ 1*(johnsonP^k)⁻¹)*(johnsonP^k*sigmaZ (-1)*(johnsonP^k)⁻¹) := by group
  rw [hp,←etaZ_shift,←etaZ_shift,←sigmaZ_shift] at h
  simpa only [add_zero,sub_eq_add_neg] using h

end
end Blueprint.HoughtonProof

#print axioms Blueprint.HoughtonProof.johnsonP
#print axioms Blueprint.HoughtonProof.johnsonQ
#print axioms Blueprint.HoughtonProof.johnsonAlpha
#print axioms Blueprint.HoughtonProof.sigmaZ
#print axioms Blueprint.HoughtonProof.etaZ
#print axioms Blueprint.HoughtonProof.johnson_relator_area
#print axioms Blueprint.HoughtonProof.sigmaZ_zero
#print axioms Blueprint.HoughtonProof.etaZ_zero
#print axioms Blueprint.HoughtonProof.sigmaZ_shift
#print axioms Blueprint.HoughtonProof.etaZ_shift
#print axioms Blueprint.HoughtonProof.johnson_alpha_square
#print axioms Blueprint.HoughtonProof.sigmaZ_square
#print axioms Blueprint.HoughtonProof.sigmaZ_inverse_close
#print axioms Blueprint.HoughtonProof.alpha_eta_area
#print axioms Blueprint.HoughtonProof.johnson_pq_close
#print axioms Blueprint.HoughtonProof.johnson_qp_close
#print axioms Blueprint.HoughtonProof.alpha_sigma_two_area
#print axioms Blueprint.HoughtonProof.sigmaZ_distance_two
#print axioms Blueprint.HoughtonProof.alpha_sigma_one_cube
#print axioms Blueprint.HoughtonProof.sigmaZ_braid_zero
#print axioms Blueprint.HoughtonProof.sigmaZ_braid
#print axioms Blueprint.HoughtonProof.etaZ_step_zero
#print axioms Blueprint.HoughtonProof.etaZ_step
