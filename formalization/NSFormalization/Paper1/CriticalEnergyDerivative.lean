import NSFormalization.Paper1.CriticalEnergyCoercivity

namespace NSFormalization.Paper1

open Set

/-- The certificate energy inequality retains half-viscosity dissipation on the open interval. -/
theorem CriticalEnergyCertificate.absorbed_energy_inequality_on_interval
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    ∀ t ∈ Ioo 0 T,
      h.energy_derivative t / 2 + (ν / 2) * (h.dissipation t) ^ 2 ≤
        h.forcing_rate t * h.norm t := by
  intro t ht
  have htcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hc : ν / 2 ≤ ν - C * h.norm t := h.dissipation_coercive t htcc
  have he := h.energy_inequality t ht
  have hsmall : C * h.norm t ≤ ν / 2 := by linarith
  exact critical_energy_absorption hsmall he

/-- The certificate controls the derivative of the squared norm by forcing. -/
theorem CriticalEnergyCertificate.energy_derivative_le
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    ∀ t ∈ Ioo 0 T,
      h.energy_derivative t ≤ 2 * h.forcing_rate t * h.norm t := by
  intro t ht
  have habs := h.absorbed_energy_inequality_on_interval t ht
  exact derivative_bound_of_absorbed_energy h.viscosity_nonneg habs

end NSFormalization.Paper1
