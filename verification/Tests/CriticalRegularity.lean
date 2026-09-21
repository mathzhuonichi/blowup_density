import Contracts.V1.CriticalRegularity
import Bindings.CriticalRegularity
import TestSupport.Axioms

/-! Public-type, statement-conformance, and transitive-axiom checks for R43 V1. -/

noncomputable section

namespace BlowupDensity.Tests

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/-- The implementation supplies the complete Proposition 4.3 interface. -/
def checkedCriticalRegularity :
    Contracts.V1.CriticalRegularity.CriticalRegularityAPI :=
  Bindings.criticalRegularity

run_cmd TestSupport.checkAxioms ``checkedCriticalRegularity

/-- Conformance with `research/R43/Spec.lean:211-217`: the general-datum field,
using the canonical registered homogeneous norm. -/
example :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (checkedCriticalRegularity.c * ν) →
            maximalLifespanR ν a f = ⊤ :=
  checkedCriticalRegularity.universal

/-- Conformance with `research/R43/Spec.lean:243-247`: the zero-datum
inhomogeneous consequence with the same structure field `c`. -/
example :
    ∀ ν : ℝ, 0 < ν →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL1 (1 / 2) f <
            ENNReal.ofReal (checkedCriticalRegularity.c * ν) →
          maximalLifespanR ν (fun _ => 0) f = ⊤ :=
  checkedCriticalRegularity.inhomogeneousAtZero

end BlowupDensity.Tests
