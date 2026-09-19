import NSFormalization.Section3.T21.Assembly

noncomputable section

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

namespace NSFormalization.Section3.T21.ReviewerNegative

/- Deliberate substantive mutation: widen the claimed non-density range from
   `s >= 1/2` to `s >= 1/4`.  The canonical theorem must not close this. -/
example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    forall nu : Real, 0 < nu -> forall s : Real, 1 / 4 <= s ->
      forall T : Real, 0 < T ->
        Not (RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)) := by
  exact nonDensity K

end NSFormalization.Section3.T21.ReviewerNegative
