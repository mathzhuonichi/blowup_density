import NSFormalization.Section3.T15.SobolevBound

noncomputable section
namespace NSFormalization.Section3.T15.Review456

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

/- Reviewer mutation: the second exponent is changed from `1/2 - s` to
`1/2 + s`.  All arguments and hypotheses of the delivered theorem remain. -/
example
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε) ≤
        ENNReal.ofReal (sobolevConst f s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 + s))) := by
  exact packetSobolevBound hf hc place

end NSFormalization.Section3.T15.Review456
