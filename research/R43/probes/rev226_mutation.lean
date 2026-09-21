import Tests.CriticalRegularity

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/-!
Reviewer negative probe: this substantively widens the universal small-data ball
from `c * ν` to `2 * c * ν`.  The checked proof must not inhabit it.
-/

example :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal
                  (2 * BlowupDensity.Tests.checkedCriticalRegularity.c * ν) →
            maximalLifespanR ν a f = ⊤ :=
  BlowupDensity.Tests.checkedCriticalRegularity.universal
