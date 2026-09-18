import NSFormalization.Section3.T16.LocalPotential

/- A substantive mutation of the API's temporal support constant: changing
   `2 * ε ^ 2` to `3 * ε ^ 2` must not be discharged by the existing field. -/
open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open NSFormalization.Section3.T16

example (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ)
    (D : CutoffData) (hD : LocalPotentialAPI v U K x₀ r T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) :
    tsupport (D.correction ε) ⊆
      Ioo (T - 3 * ε ^ 2) (T + 3 * ε ^ 2) ×ˢ (univ : Set Space) := by
  exact hD.correction_support ε hε
