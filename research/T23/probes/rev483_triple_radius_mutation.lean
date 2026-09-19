import NSFormalization.Section3.T23.Differences

noncomputable section

namespace NSFormalization.Section3.T23.Rev483TripleRadiusMutation

open Set Metric
open NavierStokes.ProblemStatement

/- Deliberately false strengthening for review: tripling the support radius is
not justified by the threshold chosen for the canonical U4 field. -/
example {u : VelocityField} {p : PressureField} {f : VelocityField}
    {K : Set Space} (place : DomainPlacementData u p f K)
    (base cutoffRadius packetRadius : ℝ) (hcutoff : 0 < cutoffRadius) :
    ∀ ε ∈ Ioc (0 : ℝ)
        (differenceThreshold place base cutoffRadius packetRadius),
      ball place.x₀ (3 * ε * diffSupportRadius cutoffRadius packetRadius) ⊆
        ball place.chartCenter place.chartRadius := by
  exact diffSupport_in_chart place base cutoffRadius packetRadius hcutoff

end NSFormalization.Section3.T23.Rev483TripleRadiusMutation
