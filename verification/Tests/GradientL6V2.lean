import Contracts.V2.GradientL6
import Bindings.GradientL6V2
import TestSupport.Axioms

/-! Public-type, conformance, and transitive-axiom checks for A05 V2. -/

noncomputable section

namespace BlowupDensity.Tests

open MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/-- The checked implementation supplies every frozen V1 field and the new
order-half critical embedding. -/
def checkedGradientL6V2 :
    Contracts.V2.GradientL6V2API Bindings.gradientL6V2Constant :=
  Bindings.gradientL6V2

run_cmd TestSupport.checkAxioms ``checkedGradientL6V2

/-- Conformance with `research/A05/Spec.lean:366-368`: the sole textual
difference in the source draft is that this statement uses the registered D01
homogeneous norm rather than the definitionally equal Spec-local copy. -/
example :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm v 3 volume ≤
        ENNReal.ofReal (Bindings.gradientL6V2Constant (1 / 2)) *
          dotHomogeneousENorm (1 / 2) v :=
  checkedGradientL6V2.velocityCriticalL3

end BlowupDensity.Tests
