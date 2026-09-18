import NSFormalization.Section3.T10.ForcePaths

noncomputable section
namespace NSFormalization.Section3.T10

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NSFormalization.Section4.A02 (SpatialField)

/- Substantive mutation: flip the Laplacian multiplier's sign. -/
example {v : SpatialField} (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 2 v)
    (i j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j : Fin 3,
      spatialPartial j (spatialPartial j (fun y ↦ (v y i : ℂ))) x) k =
      (periodicAngularFrequencySq k : ℂ) *
        periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k := by
  exact periodicFourierCoeff_component_laplacian hp hs i k

end NSFormalization.Section3.T10
