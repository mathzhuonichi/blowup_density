import Contracts.V1.CriticalFiniteHorizon
import Bindings.CriticalFiniteHorizon
import TestSupport.Axioms

/-! Public-type, statement-conformance, and transitive-axiom checks for R44 V1. -/

noncomputable section

namespace BlowupDensity.Tests

open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- The implementation supplies the complete Proposition 4.4 interface. -/
def checkedCriticalFiniteHorizon :
    Contracts.V1.CriticalFiniteHorizon.CriticalFiniteHorizonAPI :=
  Bindings.criticalFiniteHorizon

run_cmd TestSupport.checkAxioms ``checkedCriticalFiniteHorizon

/-- The checked witness uses the explicit leading coefficient from Prop44. -/
example : checkedCriticalFiniteHorizon.c =
    NSFormalization.Section4.R44.theta / 20 := rfl

/-- The checked witness uses the explicit exponential rate from Prop44. -/
example : checkedCriticalFiniteHorizon.C = 3 := rfl

/-- Conformance with the two positivity fields of the reconciled Spec. -/
example : 0 < checkedCriticalFiniteHorizon.c := checkedCriticalFiniteHorizon.hc

example : 0 < checkedCriticalFiniteHorizon.C := checkedCriticalFiniteHorizon.hC

/-- Conformance with `research/R44/Spec.lean:224-225`: the named radius is
pinned to the two preceding structure fields. -/
example : ∀ ν S : ℝ,
    checkedCriticalFiniteHorizon.radius ν S =
      checkedCriticalFiniteHorizon.c * ν ^ (3 / 2 : ℝ) *
        Real.exp (-(checkedCriticalFiniteHorizon.C * ν * S)) :=
  checkedCriticalFiniteHorizon.radiusFormula

/-- Conformance with `research/R44/Spec.lean:237`: the named radius is positive
on the positive-viscosity, positive-horizon regime. -/
example : ∀ ν S : ℝ, 0 < ν → 0 < S →
    0 < checkedCriticalFiniteHorizon.radius ν S :=
  checkedCriticalFiniteHorizon.radiusPos

/-- Conformance with `research/R44/Spec.lean:266-270`: zero-datum regularity on
the prescribed finite horizon under the inhomogeneous negative-half norm. -/
example :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1 / 2) f <
            ENNReal.ofReal (checkedCriticalFiniteHorizon.radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f :=
  checkedCriticalFiniteHorizon.main

/-- Conformance with `research/R44/Spec.lean:300-304`: the same radius excludes
the zero-datum breakdown set at the requested horizon. -/
example :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1 / 2) f <
            ENNReal.ofReal (checkedCriticalFiniteHorizon.radius ν T) →
          f ∉ breakdownSetRZero ν T :=
  checkedCriticalFiniteHorizon.nonDensityBallZero

end BlowupDensity.Tests
