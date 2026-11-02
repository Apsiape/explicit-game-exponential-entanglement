import Blueprint.A.HashNullWords

namespace Blueprint.AHash
noncomputable section
open Companion Concrete Companion.Analytic
open scoped Classical
set_option maxHeartbeats 600000

theorem clockModelHom_null_row (m k ell : Nat) (hl : ell≤m) (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell)
    (c : FiniteClock m) (hc : c∈clockInterior m ell hl) (eta : ClockHash m k)
    (hinj : Set.InjOn (hashApply eta) (hashProductSites (clockWordGammas m (w.map hashDecode) c) : Set _))
    (v : ClockRegister k) (j : ClockModelIndex m k) :
    (clockModelHom m k (FreeGroup.mk w):Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ) (c,eta,v) j=
      (1:Matrix (ClockModelIndex m k) (ClockModelIndex m k) ℂ) (c,eta,v) j := by
  have hmove := clockWordMove_null_interior m ell hl w hw hL c hc
  have hfix : (clockWordMove m (w.map hashDecode)).symm c=c := by
    apply (clockWordMove m (w.map hashDecode)).injective
    simpa only [Equiv.apply_symm_apply] using hmove.symm
  rw [clockModelHom_block]
  change (if (clockWordMove m (w.map hashDecode)).symm c=j.1 then
      clockWordFibre m k (w.map hashDecode) ((clockWordMove m (w.map hashDecode)).symm c) (eta,v) j.2 else 0)=_
  rw [hfix,clockWordFibre_null_row m k ell hl w hw hL c hc eta hinj v j.2]
  rcases j with ⟨d,j⟩
  by_cases hj : c=d <;> simp [hj,Matrix.one_apply,Prod.mk.injEq]

theorem clockWordFibre_null_defect (m k ell : Nat) (hl : ell≤m) (w : Published.HashWord)
    (hw : Published.hashGroupHom (FreeGroup.mk w)=1) (hL : w.length≤ell)
    (c : FiniteClock m) (hc : c∈clockInterior m ell hl) :
    hsNorm (clockWordFibre m k (w.map hashDecode) c-1)^2≤
      4*(ell.choose 2:ℝ)*(2:ℝ)^(-(k:ℤ))*Fintype.card (ClockFibre m k) := by
  rw [clockWordFibre_product]
  have hh := hashGammaProduct_defect (k:=k) (clockWordGammas m (w.map hashDecode) c)
    (clockWordGammas_null m ell hl w hw hL c hc)
  apply hh.trans
  have hs : (hashProductSites (clockWordGammas m (w.map hashDecode) c)).card≤ell :=
    (clockWordGammas_sites_card m _ c).trans (by simpa only [List.length_map] using hL)
  have hchoose : ((hashProductSites (clockWordGammas m (w.map hashDecode) c)).card.choose 2:ℝ)≤(ell.choose 2:ℝ) :=
    by exact_mod_cast Nat.choose_le_choose 2 hs
  gcongr

end
end Blueprint.AHash

#print axioms Blueprint.AHash.clockModelHom_null_row
#print axioms Blueprint.AHash.clockWordFibre_null_defect
