import NSFormalization.Paper1.PeriodicHeatMultiplier

noncomputable section

namespace NSFormalization.Paper1.PeriodicHeatMultiplier

/-- The heat multiplier composition law, exposed at the bounded-operator level.
This is only the already proved pointwise `heat_add` law, repackaged for CLM
applications; it does not assert existence or regularity of a PDE solution. -/
theorem heatCLM_semigroup_apply {ν s t : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : FourierHilbert) :
    heatCLM hν (add_nonneg hs ht) f =
      heatCLM hν hs (heatCLM hν ht f) := by
  simp only [heatCLM_apply]
  exact heat_add hν hs ht f

/-- Zero-time identity for the continuous-linear-map realization. -/
theorem heatCLM_zero_apply {ν : ℝ} (hν : 0 ≤ ν) (f : FourierHilbert) :
    heatCLM hν (le_refl 0) f = f := by
  simp only [heatCLM_apply]
  exact heat_zero hν f

end NSFormalization.Paper1.PeriodicHeatMultiplier

namespace NSFormalization.Paper1.PeriodicHeatMultiplier

/-- Coefficientwise heat evolution preserves addition. -/
theorem heat_add_coeff {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f g : FourierHilbert) :
    heat hν ht (f + g) = heat hν ht f + heat hν ht g := by
  change heatCLM hν ht (f + g) = heatCLM hν ht f + heatCLM hν ht g
  exact (heatCLM hν ht).map_add f g

/-- Coefficientwise heat evolution preserves complex scalar multiplication. -/
theorem heat_smul_coeff {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (c : ℂ) (f : FourierHilbert) :
    heat hν ht (c • f) = c • heat hν ht f := by
  change heatCLM hν ht (c • f) = c • heatCLM hν ht f
  exact (heatCLM hν ht).map_smul c f

end NSFormalization.Paper1.PeriodicHeatMultiplier
