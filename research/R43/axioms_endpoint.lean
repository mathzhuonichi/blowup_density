import NSFormalization.Section4.R43.Endpoint
import Bindings.MaximalPartial

open NSFormalization.Section4
open NSFormalization.Section4.A02
open NSFormalization.Section4.R43
open MeasureTheory
open scoped ENNReal

#print axioms NSFormalization.Section4.R43.criticalConst
#print axioms NSFormalization.Section4.R43.criticalConst_pos
#print axioms NSFormalization.Section4.R43.criticalConst_lt_bootstrap
#print axioms NSFormalization.Section4.R43.criticalConst_absorption
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive_le_criticalConst
#print axioms NSFormalization.Section4.R43.criticalNormAt_le_criticalConst
#print axioms NSFormalization.Section4.R43.critical_absorption_of_small_force
#print axioms NSFormalization.Section4.R43.maximal_critical_absorption
#print axioms NSFormalization.Section4.R43.maximal_h2TimeIntegral_zero_of_small_force
#print axioms NSFormalization.Section4.R43.maximal_squaredHTwoIntegral_of_small_force
#print axioms NSFormalization.Section4.R43.homogeneousAtZero_of_memForceR
#print axioms NSFormalization.Section4.R43.inhomogeneousAtZero_of_memForceR

/-- Non-vacuity: the actual small-force hypothesis holds at zero force. -/
example (ν : ℝ) (hν : 0 < ν) :
    maximalLifespanR ν (fun _ => 0) (0 : SpaceTimeField) = ⊤ := by
  apply inhomogeneousAtZero_of_memForceR ν hν 0 A04.memForceR_zero
  have hz : D01.forceSobolevENormL1 (1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ (bot_le)
    apply iInf_le_of_le ⟨fun _ => 0, (fun _ _ => D01.isSobolevDatum_zero _),
      aestronglyMeasurable_zero⟩
    simp [D01.Homogeneous.bochnerDatumENorm]
  rw [hz]
  exact ENNReal.ofReal_pos.mpr (mul_pos criticalConst_pos hν)

namespace EndpointConformance
open BlowupDensity.Contracts.V1.Data

/-- Token-for-token spec binders and Data objects, with the explicit constant. -/
theorem inhomogeneousAtZero :
    ∀ ν : ℝ, 0 < ν → ∀ f : BlowupDensity.Contracts.V1.Data.SpaceTimeField,
      BlowupDensity.Contracts.V1.Data.MemForceR f →
      BlowupDensity.Contracts.V1.Data.forceSobolevENormL1 (1 / 2) f <
        ENNReal.ofReal (criticalConst * ν) →
      BlowupDensity.Contracts.V1.Data.maximalLifespanR ν (fun _ => 0) f = ⊤ := by
  intro ν hν f hf hsmall
  rw [← BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq]
  exact inhomogeneousAtZero_of_memForceR ν hν f hf hsmall

#print axioms inhomogeneousAtZero
end EndpointConformance
