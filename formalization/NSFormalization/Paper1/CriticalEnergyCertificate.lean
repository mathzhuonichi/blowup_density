import NSFormalization.Paper1.ScalarEnergyContinuation

/-!
# Packaged critical energy certificates

This module packages the scalar hypotheses needed by the critical bootstrap.
It is deliberately a real-variable interface: no velocity field, pressure,
or PDE regularity is inferred here.  The certificate can therefore be used by
later analytic modules without silently strengthening their assumptions.
-/
namespace NSFormalization.Paper1

open Set

/-- All data entering the scalar critical bootstrap on a finite interval. -/
structure CriticalEnergyCertificate (T ν C K ρ : ℝ) where
  viscosity_nonneg : 0 ≤ ν
  coefficient_nonneg : 0 ≤ C
  radius_nonneg : 0 ≤ ρ
  radius_lt_level : ρ < K
  level_absorbs : C * K ≤ ν / 2
  norm : ℝ → ℝ
  energy_derivative : ℝ → ℝ
  dissipation : ℝ → ℝ
  forcing_rate : ℝ → ℝ
  primitive : ℝ → ℝ
  norm_continuous : Continuous norm
  norm_initial : norm 0 = 0
  norm_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ norm t
  primitive_continuous : ContinuousOn primitive (Icc 0 T)
  primitive_initial : primitive 0 = 0
  primitive_bound : ∀ t ∈ Icc 0 T, primitive t ≤ ρ
  forcing_nonneg : ∀ t ∈ Ioo 0 T, 0 ≤ forcing_rate t
  energy_derivative_spec : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun x => (norm x) ^ 2) (energy_derivative t) t
  primitive_derivative_spec : ∀ t ∈ Ioo 0 T,
    HasDerivAt primitive (forcing_rate t) t
  energy_inequality : ∀ t ∈ Ioo 0 T,
    energy_derivative t / 2 +
      (ν - C * norm t) * (dissipation t) ^ 2 ≤
      forcing_rate t * norm t

/-- A critical certificate bounds the norm by its prescribed forcing radius. -/
theorem CriticalEnergyCertificate.norm_le_radius
    {T ν C K ρ : ℝ} (h : CriticalEnergyCertificate T ν C K ρ) :
    ∀ t ∈ Icc 0 T, h.norm t ≤ ρ := by
  exact critical_norm_bound h.viscosity_nonneg h.coefficient_nonneg
    h.radius_nonneg h.radius_lt_level h.level_absorbs h.norm_continuous
    h.norm_initial h.norm_nonneg h.primitive_continuous h.primitive_initial
    h.primitive_bound h.forcing_nonneg h.energy_derivative_spec
    h.primitive_derivative_spec h.energy_inequality

end NSFormalization.Paper1
