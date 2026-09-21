import NSFormalization.Section3.T15.ConvergenceTwo

/-!
Reviewer negative probe: widening the proved `q = 2` range from `s < -1/2`
to `s < 0` must not be accepted by the delivered theorem.
-/

noncomputable section

namespace NSFormalization.Section3.T15.Rev462WidenThreshold

open Set Filter
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open scoped ENNReal Topology ContDiff

example {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < 0 →
      Tendsto (fun ε : ℝ ↦ forceSobolevENormT 2 s
        (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0) := by
  exact forceConvergence_two hf hc place

end NSFormalization.Section3.T15.Rev462WidenThreshold
