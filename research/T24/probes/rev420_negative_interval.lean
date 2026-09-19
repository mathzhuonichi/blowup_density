import NSFormalization.Section3.T24.ConservativeAssembly

noncomputable section

namespace Rev420Negative

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T24
open NSFormalization.Section4.A02 (SpatialField SpaceTimeScalar SpaceTimeField)

/- This is a substantive mutation of the registered `zero_from_rest` statement:
   the lifespan interval is changed from Ico (closed at 0, open at T) to Ioc
   (open at 0, closed at T).  The unmodified theorem must not discharge it. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0 := by
  intro ν hν T hT φ hφ S t ht x
  exact conservativeForcing.zero_from_rest ν hν T hT φ hφ S t ht x

end Rev420Negative
