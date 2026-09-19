import NSFormalization.Section3.T19.Closure

open Set Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19
open scoped ENNReal Topology

example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              ∃ ε₀ : ℝ, 0 < ε₀ ∧
                ∃ u f : ℝ → SpaceTimeField,
                  (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                    f ε ∈ forceClassT ∧
                    maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                    (∃ w : ClassicalSolutionT ν a (f ε) T, w.velocity = u ε) ∧
                    SingularTrajectoryT ν a T (u ε)) ∧
                  Tendsto
                    (fun ε : ℝ =>
                      energyENormT T (fun z => u ε z - reference.velocity z))
                    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) ∧
                  (∀ s : ℝ, s < 1 / 2 →
                    Tendsto
                      (fun ε : ℝ => forceSobolevENormT 1 s (fun z => f ε z - g z))
                      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))) := by
  exact simultaneousPairConvergence

example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
              energyENormT T (fun z => u z - u' z) < r := by
  exact closureInEnergy
