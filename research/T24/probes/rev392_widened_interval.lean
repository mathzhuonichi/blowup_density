import NSFormalization.Section3.T24.Conservative

noncomputable section

namespace NSFormalization.Section3.T24.Review392

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section4.A02 (SpatialField SpaceTimeScalar)

/- Deliberately false strengthening: widen the certified lifespan from `[0,T)`
to `[0,T]`.  The production theorem cannot supply the endpoint `t = T`. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0 := by
  intro ν hν T hT φ hφ S t ht x
  exact zero_from_rest ν hν T hT φ hφ S t ht x

end NSFormalization.Section3.T24.Review392
