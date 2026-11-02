import Blueprint.A.SectorEntropyProof

namespace Blueprint.Published
noncomputable section
open Companion Companion.Analytic

/-- Exact statement of Mghirbi--Douglas v1.0.0, Lemma 4.7.
The proof `sectorEntropy` below retains the binary correction and rank bound. -/
def SectorEntropy : Prop := ∀ (d : Nat) (s : State d) (J : Mat d), IsInvolution J →
  ∀ t : State d, 0<(signProjection J true*s.rho).trace.re →
  t.rho=(((signProjection J true*s.rho).trace.re:ℂ)⁻¹) •
    (signProjection J true*s.rho*signProjection J true) →
  (signProjection J true*s.rho).trace.re*entropy t.rho-
    binaryEntropy (min (hs (comm J s.xi)^2/4) (1/2))≤entropy s.rho ∧ rank t.rho≤rank s.rho

/-- The paper's sector entropy lemma, proved from pinching and Jensen--Shannon. -/
theorem sectorEntropy : SectorEntropy := by
  intro d s J hJ t hp ht
  exact ASectorProof.sector_entropy_from_pinching s t J hJ hp ht

end
end Blueprint.Published

namespace Blueprint.ASectorProof
noncomputable section
open Companion Companion.Analytic Published

theorem sector_entropy_bound {d : Nat} (s t : State d) (J : Mat d)
    (hJ : IsInvolution J) (hp : 0<(signProjection J true*s.rho).trace.re)
    (ht : t.rho=(((signProjection J true*s.rho).trace.re:ℂ)⁻¹) •
      (signProjection J true*s.rho*signProjection J true))
    (delta : ℝ) (hdelta : delta^2/16≤(signProjection J true*s.rho).trace.re) :
    entropy t.rho*delta^2/16-1≤entropy s.rho ∧ rank t.rho≤rank s.rho := by
  obtain ⟨hent,hrank⟩ := Published.sectorEntropy d s J hJ t hp ht
  have hb : binaryEntropy (min (hs (comm J s.xi)^2/4) (1/2))≤1 :=
    (div_le_one (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr Real.binEntropy_le_log_two
  have hn := entropy_nonneg t
  have hh := mul_le_mul_of_nonneg_left hdelta hn
  exact ⟨by nlinarith,hrank⟩

end
end Blueprint.ASectorProof

#print axioms Blueprint.Published.SectorEntropy
#print axioms Blueprint.Published.sectorEntropy
#print axioms Blueprint.ASectorProof.sector_entropy_bound
