import NSFormalization.Section3.T10.FourierCalculus

open NSFormalization.Section3.T10 NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open scoped ContDiff BigOperators

-- Deliberately false mutation: the Laplacian multiplier's minus sign is flipped.
example {f : Space → ℂ} (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ 2 f)
    (k : PeriodicFrequency) :
    periodicFourierCoeff
        (fun x ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j f) x) k =
      ((4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) *
        periodicFourierCoeff f k := by
  simpa using periodicFourierCoeff_laplacian hp hs k

