import NSFormalization.Section3.T15.Convergence

noncomputable section

namespace NSFormalization.Section3.T15.Review458Mutation

open Set Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal Topology

example : alphaT 2 2 = -(1 : ℝ) / 2 := by
  norm_num [alphaT]

example : criticalOrder ((1 : ℝ≥0∞).toReal) = (1 : ℝ) / 2 := by
  norm_num [criticalOrder]

example : criticalOrder ((2 : ℝ≥0∞).toReal) = -(1 : ℝ) / 2 := by
  norm_num [criticalOrder]

/- Review mutation: widening the proved `q = 1` range from `s < 1/2` to
`s < 3/2` must not be discharged by `forceConvergence_one`. -/
example {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < criticalOrder ((1 : ℝ≥0∞).toReal) + 1 →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (periodizedScaledForce f place.x₀ place.T ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact forceConvergence_one hf hc place

end NSFormalization.Section3.T15.Review458Mutation
