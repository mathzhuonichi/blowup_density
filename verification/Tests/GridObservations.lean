import Contracts.V1.GridObservations
import Bindings.GridObservations
import TestSupport.Axioms

/-! Public statement conformance and transitive axiom audit for R47 V1. -/

noncomputable section

namespace BlowupDensity.Tests

open NavierStokes.ProblemStatement
open Contracts.V1.Data
open Contracts.V1.GridObservations

theorem checkedGridObservations : GridObservationsAPI :=
  Bindings.gridObservations

run_cmd TestSupport.checkAxioms ``checkedGridObservations

/-- Conformance with `research/R47/Spec.lean`'s `RGridAPI.choose`. -/
example :
    ∀ ν : ℝ, 0 < ν →
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ g : SpaceTimeField, MemForceR g →
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
    ∀ reference : ClassicalSolutionR ν a g (T + δ),
    ∀ n : ℕ, ∀ grids : Fin n → Grid,
      Nonempty (GridFamilyAPI ν a g T δ reference n grids) :=
  checkedGridObservations.choose

end BlowupDensity.Tests
