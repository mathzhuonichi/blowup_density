import Tests.CriticalRegularity

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

#print axioms NSFormalization.Section4.R43.criticalConst
#print axioms NSFormalization.Section4.R43.criticalConst_pos
#print axioms NSFormalization.Section4.R43.universal_of_memForceR
#print axioms NSFormalization.Section4.R43.inhomogeneousAtZero_of_memForceR
#print axioms BlowupDensity.Bindings.criticalRegularity_initialClassR_eq
#print axioms BlowupDensity.Bindings.criticalRegularity_memForceR_eq
#print axioms BlowupDensity.Bindings.criticalRegularity_dotHomogeneousENorm_eq
#print axioms BlowupDensity.Bindings.criticalRegularity_forceHomogeneousENorm_eq
#print axioms BlowupDensity.Bindings.criticalRegularity_forceSobolevENormL1_eq
#print axioms BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq
#print axioms BlowupDensity.Bindings.criticalRegularity
#print axioms BlowupDensity.Tests.checkedCriticalRegularity

noncomputable section
namespace CriticalRegularityContractConformance

/-- The general field in literal `Contracts.V1.Data` vocabulary, with the
explicit implementation constant substituted for the Spec's structure field. -/
theorem universal :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (NSFormalization.Section4.R43.criticalConst * ν) →
            maximalLifespanR ν a f = ⊤ :=
  BlowupDensity.Tests.checkedCriticalRegularity.universal

/-- The zero-datum field in literal `Contracts.V1.Data` vocabulary, with the
same explicit constant and the inhomogeneous force norm. -/
theorem inhomogeneousAtZero :
    ∀ ν : ℝ, 0 < ν →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL1 (1 / 2) f <
            ENNReal.ofReal (NSFormalization.Section4.R43.criticalConst * ν) →
          maximalLifespanR ν (fun _ => 0) f = ⊤ :=
  BlowupDensity.Tests.checkedCriticalRegularity.inhomogeneousAtZero

/-- The public record stores the documented explicit radius. -/
theorem constant_value :
    BlowupDensity.Tests.checkedCriticalRegularity.c =
      min (1 / (8 * NSFormalization.Section4.R43.trilinearConst))
        (1 / (4 * (NSFormalization.Section4.A05.gradientL6Const *
          NSFormalization.Section4.A05.criticalL3Const))) := rfl

#print axioms universal
#print axioms inhomogeneousAtZero
#print axioms constant_value

end CriticalRegularityContractConformance
