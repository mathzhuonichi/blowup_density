import NSFormalization.Section3.T21.Ball
import NSFormalization.Section3.T21.NonDensity
import NSFormalization.Section3.T21.OrderLowering

/-!
# T21 canonical non-density assembly
-/

noncomputable section

namespace NSFormalization.Section3.T21
set_option linter.defProp false

/-- The complete canonical nine-field `cor:nondensity` package associated to
any T20 critical-regularity package. -/
def nonDensityAPI
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    NonDensityAPI K.c where
  hc := K.hc
  criticalGlobalRegularity := criticalGlobalRegularity K
  zeroMemBall := zeroMemBall K.c K.hc
  ballRelativelyOpen := ballRelativelyOpen K.c
  sliceSobolevMonotone := sliceSobolevMonotone
  forceSobolevMonotone := forceSobolevMonotone
  criticalBallDisjoint := criticalBallDisjoint K
  ballDisjoint := ballDisjoint K
  nonDensity := nonDensity K

/-- The canonical arrow-type formulation of the T21 construction. -/
def nonDensityOfCritical : Prop :=
  ∀ K : NSFormalization.Section3.T20.CriticalRegularityTAPI,
    NonDensityAPI K.c

/-- The canonical arrow-type construction is inhabited. -/
theorem nonDensityOfCritical_holds : nonDensityOfCritical :=
  nonDensityAPI

/-- The paper-order non-density statement follows from each assembled
critical-regularity package. -/
theorem nonDensityStatement_holds
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    nonDensityStatement :=
  (nonDensityAPI K).nonDensity

end NSFormalization.Section3.T21
