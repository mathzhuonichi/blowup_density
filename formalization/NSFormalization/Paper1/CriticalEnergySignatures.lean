import NSFormalization.Paper1.CriticalEnergyDerivative

namespace NSFormalization.Paper1

open Set

/-- The absorbed nonlinear coefficient is nonnegative on the certified interval. -/
theorem CriticalEnergyCertificate.dissipation_coefficient_nonneg
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    ∀ t ∈ Icc 0 T, 0 ≤ ν - C * h.norm t := by
  intro t ht
  have hc := h.dissipation_coercive t ht
  have hv : 0 ≤ ν / 2 := div_nonneg h.viscosity_nonneg (by norm_num)
  linarith

/-- The forcing work term is nonnegative on the open energy interval. -/
theorem CriticalEnergyCertificate.forcing_work_nonneg
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    ∀ t ∈ Ioo 0 T, 0 ≤ h.forcing_rate t * h.norm t := by
  intro t ht
  exact mul_nonneg (h.forcing_nonneg t ht)
    (h.norm_nonneg t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-- The squared norm starts at zero, as required by packet-energy interfaces. -/
theorem CriticalEnergyCertificate.norm_sq_initial
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    h.norm 0 ^ 2 = 0 := by
  rw [h.norm_initial]
  norm_num

end NSFormalization.Paper1
