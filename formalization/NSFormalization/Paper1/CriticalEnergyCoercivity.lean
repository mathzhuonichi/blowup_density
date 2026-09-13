import NSFormalization.Paper1.CriticalEnergyCertificate

/-!
# Coercivity extracted from a critical energy certificate

This is the scalar positivity estimate used when applying the energy inequality.
It does not construct a flow or add any PDE regularity.
-/
namespace NSFormalization.Paper1

open Set

/-- The nonlinear dissipation coefficient remains at least half the viscosity
throughout a certified critical interval. -/
theorem CriticalEnergyCertificate.dissipation_coercive
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    ∀ t ∈ Icc 0 T, ν / 2 ≤ ν - C * h.norm t := by
  intro t ht
  have hynorm : h.norm t ≤ ρ := h.norm_le_radius t ht
  have hCrho : C * h.norm t ≤ C * ρ :=
    mul_le_mul_of_nonneg_left hynorm h.coefficient_nonneg
  have hρK : C * ρ ≤ C * K := by
    exact mul_le_mul_of_nonneg_left h.radius_lt_level.le h.coefficient_nonneg
  nlinarith [h.level_absorbs, hCrho, hρK]

end NSFormalization.Paper1
