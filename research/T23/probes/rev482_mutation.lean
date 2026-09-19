import NSFormalization.Section3.T23.Solution

namespace NSFormalization.Section3.T23.InsertedTriple

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

variable {nu delta r : ℝ} {Omega K : Set Space}
  {a : SpatialField} {g : SpaceTimeField}
  {u f : VelocityField} {p : PressureField}
  {place : DomainPlacementData u p f K} {D : CutoffData}
  {reference : ClassicalSolutionOmega nu Omega a g (place.T + delta)}

/- Mutation: widening the quiet-history endpoint from `T - 2 * eps^2` to
`T - eps^2` must not be discharged by the production history theorem. -/
example (C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T delta D)
    {eps : ℝ} (heps : eps ∈ Ioc 0 D.ε₀) {t : ℝ}
    (ht : t ≤ place.T - eps ^ 2) (x : Space) :
    velocity place D reference eps (t, x) = reference.velocity (t, x) := by
  exact history C heps ht x

end NSFormalization.Section3.T23.InsertedTriple
