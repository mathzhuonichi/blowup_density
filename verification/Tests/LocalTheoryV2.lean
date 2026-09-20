import Contracts.V2.LocalTheory
import Bindings.LocalTheoryV2
import TestSupport.Axioms

/-!
# Acceptance test for A01 local theory V2

The examples repeat the public fields in the shapes of
`research/A01/Spec.lean`.  The last two examples distinguish the registered
fixed-force H⁷ field from the separately named, unregistered H¹ predicate.
-/

noncomputable section

namespace BlowupDensity.Tests

open Set
open Contracts.V1.Data
open Contracts.V2
open scoped ENNReal

/-- The implementation supplies the complete version-two interface. -/
def checkedLocalTheoryV2 : LocalTheory.LocalTheoryAPI :=
  Bindings.localTheoryV2

run_cmd TestSupport.checkAxioms ``checkedLocalTheoryV2

/-! Conformance with `research/A01/Spec.lean:277-345`, except for the
owner-approved and explicitly documented quantitative narrowing. -/

example : ℝ → SpatialField → SpaceTimeField → ℝ :=
  checkedLocalTheoryV2.horizon

example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ClassicalSolutionR ν a f (checkedLocalTheoryV2.horizon ν a f) :=
  checkedLocalTheoryV2.solution

example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f),
      LocalTheory.ManuscriptLocalRegularity ν a f (checkedLocalTheoryV2.horizon ν a f)
        (checkedLocalTheoryV2.solution ν a f hν ha hf) :=
  checkedLocalTheoryV2.regularity

/-- Registered V2 field: H⁷ data, with the force fixed before `∃ δ`. -/
example :
    ∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ initialClassR → sobolevENorm 7 a ≤ K →
        δ ≤ checkedLocalTheoryV2.horizon ν a f :=
  checkedLocalTheoryV2.horizon_lower_bound

/-- The paper's H¹/cross-force sentence is only a definition.  This `rfl`
checks its wording; it does not inhabit the predicate. -/
example : LocalTheory.ManuscriptHorizonLowerBoundH1 checkedLocalTheoryV2 =
    (∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (a : SpatialField) (f : SpaceTimeField),
          a ∈ initialClassR → MemForceR f →
            sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
              δ ≤ checkedLocalTheoryV2.horizon ν a f) := rfl

/-- Structural V1 compatibility is part of the V2 acceptance surface. -/
example :
    Contracts.V1.RegularityPartial.ManuscriptLocalRegularityPartialAPI :=
  Bindings.regularityPartial_of_v2

end BlowupDensity.Tests
