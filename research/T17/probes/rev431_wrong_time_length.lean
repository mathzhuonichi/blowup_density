import NSFormalization.Section3.T17.ForceVolume

/-! Reviewer negative probe: the canonical duration `4ε²` is mutated to `2ε²`.
This file is expected not to compile. -/

noncomputable section

namespace NSFormalization.Section3.T17.ReviewerProbe

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology ENNReal

example (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      volume (torusTemporalSupport
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (2 * ε ^ 2) := by
  exact force_time_length ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc
    hθsupp hηsupp hr2 hεtime hεspace

end NSFormalization.Section3.T17.ReviewerProbe
