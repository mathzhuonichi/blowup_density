import Contracts.V1.CompletedDensity
import Bindings.CompletedDensity
import TestSupport.Axioms

/-! Public statement conformance and transitive axiom checks for R46 V1. -/

noncomputable section

namespace BlowupDensity.Tests

open Set Filter
open Contracts.V1 Contracts.V1.Data
open scoped ENNReal Topology

/-- The implementation supplies the complete Proposition 4.6 interface. -/
theorem checkedCompletedDensity :
    Contracts.V1.CompletedDensity.CompletedDensityAPI :=
  Bindings.completedDensity

run_cmd TestSupport.checkAxioms ``checkedCompletedDensity

/-- Conformance with `REnergyAPI.completedSobolevDensity`. -/
example :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
            ∀ s : ℝ, s < criticalOrder q.toReal →
              CompletedDense q s
                (breakdownSetIn forceClassCompact ν a T) :=
  checkedCompletedDensity.completedSobolevDensity

/-- Conformance with `REnergyAPI.completedHomogeneousDensity`. -/
example :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          CompletedDenseHomogeneous 2 (-1)
            (breakdownSetIn forceClassCompact ν a T) :=
  checkedCompletedDensity.completedHomogeneousDensity

/-- Conformance with `REnergyAPI.strongTrajectoryClosure`. -/
example :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ g : SpaceTimeField, MemForceR g →
            ∀ δ : ℝ, 0 < δ →
              ∀ R : ClassicalSolutionR ν a g (T + δ),
                ∃ (P : PacketAPI ν) (A : InsertionFamilyAPI ν P),
                  A.a = a ∧
                  A.scaling.correction.T = T ∧
                  A.scaling.correction.g = g ∧
                  A.scaling.correction.v = R.velocity ∧
                  A.scaling.correction.π = R.pressure ∧
                  (∀ ε ∈ Ioc (0 : ℝ) A.ε₀,
                    MemForceR (A.force ε) ∧
                    maximalLifespanR ν a (A.force ε) = ENNReal.ofReal T ∧
                    ∃ U : ClassicalSolutionR ν a (A.force ε) T,
                      U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε) ∧
                  Tendsto (fun ε : ℝ => energyENorm T
                    (fun z => A.velocity ε z - R.velocity z))
                    (𝓝[>] 0) (𝓝 0) ∧
                  Tendsto (fun ε : ℝ =>
                    forceSobolevENorm 1 0 (fun z => A.force ε z - g z) +
                    forceSobolevENorm 2 (-1) (fun z => A.force ε z - g z) +
                    forceHomogeneousENorm 2 (-1) (fun z => A.force ε z - g z))
                    (𝓝[>] 0) (𝓝 0) :=
  checkedCompletedDensity.strongTrajectoryClosure

end BlowupDensity.Tests
