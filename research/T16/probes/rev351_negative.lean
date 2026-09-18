import NSFormalization.Section3.T16.BallPotential

/-!
Negative review probe: mutate the canonical potential formula by flipping its sign.
The original hypotheses and all three witness clauses are retained; reusing
`exists_potential_on_ball` must fail at the mutated formula, rather than by
dropping an argument or making the instance vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T16.ReviewProbe

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement NavierStokes.SpatialCurl
open NSFormalization.Paper1.RadialPotential (cross)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T16
open scoped ContDiff Topology

example {v : SpaceTimeField} {x₀ : Space} {r T δ : ℝ}
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ A : SpaceTimeField,
      ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) ∧
      (∀ t x, A (t, x) = -∫ ρ in (0 : ℝ)..1,
        ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)) ∧
      (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
        SpatialCurl.curl (fun y => A (t, y)) x = v (t, x)) := by
  obtain ⟨A, hA, hformula, hcurl⟩ := exists_potential_on_ball hv hdiv
  refine ⟨A, hA, ?_, hcurl⟩
  intro t x
  exact hformula t x

end NSFormalization.Section3.T16.ReviewProbe
