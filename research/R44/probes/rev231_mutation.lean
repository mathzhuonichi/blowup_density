import Tests.CriticalFiniteHorizon

open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-!
Reviewer negative probe: this substantively widens the main theorem's force ball
from `radius ν S` to `2 * radius ν S`.  The checked proof must not inhabit it.
-/

example :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1 / 2) f <
            ENNReal.ofReal
              (2 * BlowupDensity.Tests.checkedCriticalFiniteHorizon.radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f :=
  BlowupDensity.Tests.checkedCriticalFiniteHorizon.main
