import Bindings.CompletedDensity

noncomputable section

open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings

/- Deliberate mutation: replace the homogeneous Sobolev order `-1` by `0`.
The registered proof must not inhabit this materially stronger statement. -/
example :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          CompletedDenseHomogeneous 2 0
            (breakdownSetIn forceClassCompact ν a T) :=
  completedDensity.completedHomogeneousDensity
