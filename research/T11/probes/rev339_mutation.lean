import NSFormalization.Section3.T11.ClassicalRegularity
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NavierStokes.ProblemStatement
-- Mutation: weaken the viscosity guard from 0 < ν to 0 ≤ ν.
example : ∀ (ν : ℝ), 0 ≤ ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          PeriodicLocalRegularity ν a f T w := by
  intro ν hν a ha f hf T w
  exact periodicLocalRegularity_of_classical ν hν a ha f hf T w
