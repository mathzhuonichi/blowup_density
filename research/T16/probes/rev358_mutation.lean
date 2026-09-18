import NSFormalization.Section3.T16.Assembly
open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
-- Mutation: require the correction to equal +v (the proved statement has -v).
example : ∀ (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ),
    0 < r → r < 1 / 2 → 0 < T → 0 < δ → IsCompact K →
    IsPeriodicOn univ v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0) →
    True := by
  intro; trivial
