import Contracts.V1.Data

open BlowupDensity.Contracts.V1.Data

/- The R46 and R47 first summands use different registered carriers; this is
deliberately expected not to close by definitional equality. -/
example (f : SpaceTimeField) :
    forceSobolevENorm 1 0 f = mixedLebesgueENorm 1 2 f := by
  rfl
