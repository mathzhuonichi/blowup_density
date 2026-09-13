import NSFormalization.Paper1.CriticalEnergySignatures

namespace NSFormalization.Paper1

open Set

/-- On a certified interval, forcing work is bounded by the forcing rate times
its prescribed radius.  This is a scalar pointwise consequence of the critical
certificate, with no PDE or regularity conclusion. -/
theorem CriticalEnergyCertificate.forcing_work_le_radius
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    ∀ t ∈ Ioo 0 T,
      h.forcing_rate t * h.norm t ≤ h.forcing_rate t * ρ := by
  intro t ht
  have htcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hnorm : h.norm t ≤ ρ := h.norm_le_radius t htcc
  exact mul_le_mul_of_nonneg_left hnorm (h.forcing_nonneg t ht)

end NSFormalization.Paper1
