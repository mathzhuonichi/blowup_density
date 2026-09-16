import Bindings.DensityFromInsertion

open BlowupDensity.Bindings BlowupDensity.Contracts.V1.Data
open scoped ENNReal

#print axioms density_forceSobolevENorm_zero
#print axioms breakdownDenseR_of_subcritical
#print axioms breakdownDenseR_zero_of_subcritical

namespace BlowupDensity.Bindings.DensityAudit

/-- Concrete density at viscosity/time one and q=1, s=0. -/
theorem zero_density : BreakdownDenseR 1 0 1 1 0 := by
  apply breakdownDenseR_zero_of_subcritical 1 1 zero_lt_one zero_lt_one 1
    (Or.inl rfl) 0
  norm_num

/-- The zero reference is admissible and has breakdown approximants in every ball. -/
theorem zero_reference : ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ breakdownSetR 1 0 1, forceSobolevENorm 1 0 (f - 0) < r := by
  exact zero_density 0 NSFormalization.Section4.A04.memForceR_zero

example : ∃ f ∈ breakdownSetR 1 0 1, forceSobolevENorm 1 0 (f - 0) < 1 :=
  zero_reference 1 zero_lt_one

#print axioms zero_density
#print axioms zero_reference

end BlowupDensity.Bindings.DensityAudit
